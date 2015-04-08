// Thunks to implement lazy evaluation
// 
// We memoize this, so the G modality can't use this 
// implementation of thunks -- it just uses nullary 
// functions since it needs call-by-name behavior for 
// correctness. 
//
function Lazy(fn) {
    this.code = fn;
    this.value = null;
    this.evaluated = false;
}
Lazy.prototype.force  = function () {
    if (this.evaluated) {
	return this.value;
    } else {
	let f = this.code;
	this.value = f(); // avoids passing the thunk as 'this'
	return this.value;
    }
}

// The Thunk operator
//
// This does nothing. 

function Thunk(thunk) { 
    return thunk;
}

////////////////

//
// interface Cons a = {
//    head : () -> a;
//    tail : () -> Lazy (Cons a)
// }

// The naive implementation. 
//
function Cons(h, t) {
    this.hd = h;
    this.tl = t;
}
Cons.prototype.head = function () {
    return this.hd;
}
Cons.prototype.tail = function () {
    return this.tl;
}

// Turn async events into synchronous streams
//
// The idea behind is that we have an event which periodically 
// evaluates its event handlers at unknown times. We want to turn the
// event into a data stream, so we create a new piece of memory 
// this.buffer, and attach an event handler which updates this.buffer.
//
// When we force the tail of the stream, we copy the value of this.buffer
// into this.head, giving us the new value of the stream for this tick. 
// So if the event handler is called multiple times during a tick, the 
// last value wins.
//
// Furthermore, we only want to copy the buffer once per tick, but we can 
// create multiple aliases to the tail of the stream. So we also have a flag 
// variable, which tail checks before doing the move. This ensures that the 
// copy is dones at most once. 
//
// Furthermore, if the copy is never done, that's fine! This means no one
// will ever look at the stream in the future, so there's no need to update
// the event stream. 

function EventStream(noEvent, onEvent) {
    let stream = this;
    stream.noEvent = noEvent;
    stream.hd = noEvent;
    //
    stream.buffer = noEvent;
    stream.tick = false;
    //
    onEvent(function (v) { stream.buffer = v; });
}
EventStream.prototype.head = function () { 
    return this.hd;
}
EventStream.prototype.tail = function () {
    let stream = this;
    let old_tick = this.tick;
    function thunk () {
	if (stream.tick === old_tick) {
	    stream.tick = !stream.tick;
	    stream.hd = stream.buffer;
	    stream.buffer = stream.noEvent;
	}
	return stream;
    }
    return (new Lazy(thunk));
}

// Take a nullary event like onClick and generate a stream of booleans
// saying whether the event happened this tick. 

function booleanEventStream(onEvent) {
    return new EventStream(false,
			   function (f) {
			       onEvent(function () { f(true); });
			   });
}

// Take a stream of keyboard events and generate a stream of option string
// saying whether the event happened, and what the string was. 

function keyboardEventStream(onEvent) {
    let none = ["None", []];
    let some = function(v) { return ["Some", v]; };
    return new EventStream(none,
                           function(f) {
                               onEvent(function(evt) { f(some(String.fromCharCode(evt.charCode))); }); 
                           });
}


////////////////

function lazyfix(f) {
    return f(new Lazy(function () { return lazyfix(f); }));
}

function toString (n) {
    return n.toString();
}

function cat (pair) {
    return pair[0] + pair[1];
}

//////////////// Widgets ////////////////
//
// Widgets are basically DOM nodes, plus two extra properties.
// First, we add a tickQueue property, which queues the actions to
// perform on the node at the end of a timestep.
// 
// Second, we have a maybeText property, which is either false (if the
// DOM node does not have a text node as a direct subchild), or is a
// text node (if the DOM node has that text node as a direct subchild).
//
// We use maybeText to give a simpler API for updating the 

// The step function executes all of the queued actions on each widget, 
// when a tick happens. It does this bottom-up, updating all the children
// of a DOM node before updating the node. 

function isWidget(node) {
    return node.hasOwnProperty('tickQueue');
}

function $step(widget) {
    let children = widget.childNodes;    
    let i = 0;
    let len = children.length;
    while (i < len) {
	if (isWidget(children.item(i))) {
	    $step(children.item(i));
	}
	i = i + 1;
    }
    //
    let todo = widget.tickQueue;
    widget.tickQueue = [];
    todo.forEach(function(thunk) { thunk.force(); });
}

// Now, here are the operations to build and modify widgets 

function mkText(label) {
    return (function () { 
        let text = document.createTextNode(label);
        let span = document.createElement("span");
        span.appendChild(text);
        span.tickQueue = [];
        span.maybeText = text;
        return span;
    });
}

function mkButton() {
    let b = document.createElement("button");
    b.tickQueue = [];
    b.maybeText = false;
    return b;
}


function hbox() {
    let elt = document.createElement("div");
    elt.style.display="block";
    elt.maybeText = false;
    elt.tickQueue = [];
    return elt;
}

function vbox() { 
    let elt = document.createElement("div");
    elt.style.display='inline';
    elt.maybeText = false;
    elt.tickQueue = [];
    return elt;
}    

function attachOp(args) {
    let w1 = args[0];
    let w2 = args[1];
    w1.appendChild(w2);
    return w1;
}

function attach() {
    return attachOp;
}


//////////////// Splitting and merging widgets ////////////////
//
// Both the frame type and the widget type are represented by DOM
// nodes. However, when we join a frame and its future thunk, we 
// push that thunk onto the list of actions for the widget. This
// lets us update the node when a tick happens. 

function splitOp(widget) {
    return [widget, new Lazy(function () { return widget; })];
}

function split() {
    return splitOp;
}

function mergePrim(w0, wlazy) {
    w0.tickQueue.push(wlazy);
    return w0;
}

function mergeOp(args) {
    let w0 = args[0];
    let wlazy = args[1];
    w0.tickQueue.push(wlazy);
    return w0;
}

function merge() {
    return mergeOp;
}

function dropOp(w) {
    return new Lazy(function () { return widget; });
}



//////////////// Operations to modify widgets ////////////////

function text(txt) {
    return (function () {
        return (function (widget) {
            let new_text = document.createTextNode(txt);
            if (widget.maybeText) {
                widget.replaceChild(new_text, widget.maybeText);
            } else {
                widget.appendChild(new_text);
            }
            widget.maybeText = new_text;
            return widget;
        });
    });
}

function color(colorname) {
    return (function () {
        return (function (widget) {
            widget.style.color = colorname;
            return widget;
        });
    });
}

function backgroundColor(colorname) {
    return (function () {
        return (function (widget) {
            widget.style.color = colorname;
            return widget;
        });
    });
}


function font(fontname) {
    return (function () {
        return (function (widget) {
            widget.style.font = fontname;
            return widget;
        });
    });
}

function fontFamily(family) {
    return (function () {
        return (function (widget) {
            widget.style.fontFamily = family;
            return widget;
        });
    });
}

function width(w) {
    return (function () {
        return (function (widget) {
            widget.style.width = w;
            return widget;
        });
    });
}


//////////////// Events 
//
// Events work by taking a widget, and attaching a listener for an event
// to it. For linearity's sake we return the argument as well. 

function clicksOp (elt) {
    let bs = booleanEventStream(function(f) { elt.addEventListener("click", f, false); });
    return [elt, bs];
}

function clicks() {
    return clicksOp;
}

function mouseOverOp (elt) {
    let bs = booleanEventStream(function(f) { elt.addEventListener("mouseover", f, false); });
    return [elt, bs];
}

function mouseover() {
    return mouseOverOp;
}

function keypressOp (elt) {
    let ks = keyboardEventStream(function (f) { elt.addEventListener("keypress", f, false); });
    return [elt, ks];
}

function keypress() {
    return keypressOp;
}


////////////////

function repeat(thunk, n) {
    function repeater() { 
      thunk();
      window.setTimeout(repeater, n);
    }
    window.setTimeout(repeater, n);
}

function $start(app_root, app) {
    let widget = app();
    document.getElementById(app_root).appendChild(widget);
    repeat(function () { $step(widget); }, 25);
}
