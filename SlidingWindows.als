sig State {
	windows: set Window
}

sig Window {
	item: lone Number
}

abstract sig Number {}

one sig One, Two, Three, Four, Five, Six, Seven, Eight extends Number {}

fact {
	all n: Number| (n in State.windows.item) and lone w: Window| n in w.item
}

fact {
	all s: State| #s.windows = 9
}

pred show {}

run show for 10
