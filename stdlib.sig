// types

type option a = None | Some of a
type list a = Nil | Cons of a × list a

// utility functions

val toString : num → string
val cat    : string × string → string

// Widget construction 

val mkText   : string → G(∃ a. dom a)
val mkButton : G(∃ a. dom a)
val vbox     : G(∃ a. dom a)
val hbox     : G(∃ a. dom a)

val attach : G(∀ a b. dom a ⊗ dom b ⊸ dom a)

// Widget modification 

val backgroundColor : string → G(∀ a. dom a ⊸ dom a)
val color           : string → G(∀ a. dom a ⊸ dom a)
val font            : string → G(∀ a. dom a ⊸ dom a)
val fontFamily      : string → G(∀ a. dom a ⊸ dom a)
val width           : string → G(∀ a. dom a ⊸ dom a)
val text            : string → G(∀ a. dom a ⊸ dom a)
val width           : string → G(∀ a. dom a ⊸ dom a)

// Widget dynamics 

val split : G(∀ a. dom a ⊸ frame a ⊗ next(dom a))
val merge : G(∀ a. frame a ⊗ next(dom a) ⊸ dom a)

// Event processing

val mouseover    : G(∀ a. dom a ⊸ dom a ⊗ F (stream bool))
val clicks       : G(∀ a. dom a ⊸ dom a ⊗ F (stream bool))
val keypress     : G(∀ a. dom a ⊸ dom a ⊗ F (stream (option string)))

// val doubleclicks : G(∀ a. dom a ⊸ dom a ⊗ F (stream bool))

