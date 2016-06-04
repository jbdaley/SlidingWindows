// Needed to create an ordering of states, from initial to the solution state
open util/ordering[State]

// Uncertain if this will be needed
open util/relation

// An instance of the game board's state
sig State {
	windows: set Window
}

// A position on the board
abstract sig Window {
	item: lone Number,
	neighbor: set Window
}
// The actual positions on the board
sig WZero, WOne, WTwo, WThree, WFour, WFive, WSix, WSeven, WEight extends Window {}

// A tile
abstract sig Number {
	parent: one Window
}
// Title instances
one sig One, Two, Three, Four, Five, Six, Seven, Eight extends Number {}

// This is useful to find which position a number is at on a given board... I'm not sure if this will
// be used when we're done.
fact ParentItemRelationship {
	parent = ~item
}

// The positions on the board can be though of as a graph. The vertices are the positions on the board
// and the edges are the neighboring relationships between positions.
// Each state (instance of a game board) needs its own graph
fact WindowGraph {
	all s: State| {
		one w: s.windows & WZero| {
			#w.neighbor = 2
			one a: s.windows & WOne| a in w.neighbor
			one b: s.windows & WThree| b in w.neighbor
		}
		one w: s.windows & WOne| {
			#w.neighbor = 3
			one a: s.windows & WZero| a in w.neighbor
			one b: s.windows & WTwo| b in w.neighbor
			one c: s.windows & WFour| c in w.neighbor
		}
		one w: s.windows & WTwo| {
			#w.neighbor = 2
			one a: s.windows & WOne| a in w.neighbor
			one b: s.windows & WFive| b in w.neighbor
		}
		one w: s.windows & WThree| {
			#w.neighbor = 3
			one a: s.windows & WZero| a in w.neighbor
			one b: s.windows & WFour| b in w.neighbor
			one c: s.windows & WSix| c in w.neighbor
		}
		one w: s.windows & WFour| {
			#w.neighbor = 4
			one a: s.windows & WOne| a in w.neighbor
			one b: s.windows & WThree| b in w.neighbor
			one c: s.windows & WFive| c in w.neighbor
			one d: s.windows & WSeven| d in w.neighbor
		}
		one w: s.windows & WFive| {
			#w.neighbor = 3
			one a: s.windows & WTwo| a in w.neighbor
			one b: s.windows & WFour| b in w.neighbor
			one c: s.windows & WEight| c in w.neighbor
		}
		one w: s.windows & WSix| {
			#w.neighbor = 2
			one a: s.windows & WThree| a in w.neighbor
			one b: s.windows & WSeven| b in w.neighbor
		}
		one w: s.windows & WSeven| {
			#w.neighbor = 3
			one a: s.windows & WSix| a in w.neighbor
			one b: s.windows & WFour| b in w.neighbor
			one c: s.windows & WEight| c in w.neighbor
		}
		one w: s.windows & WEight| {
			#w.neighbor = 2
			one a: s.windows & WSeven| a in w.neighbor
			one b: s.windows & WFive| b in w.neighbor
		}
	}
}

// Each game board should include every number
fact AllNumbersInEachState {
	all s: State| {
		one n: One| n in s.windows.item
		one n: Two| n in s.windows.item
		one n: Three| n in s.windows.item
		one n: Four| n in s.windows.item
		one n: Five| n in s.windows.item
		one n: Six| n in s.windows.item
		one n: Seven| n in s.windows.item
		one n: Eight| n in s.windows.item
	}  
}

// Each board position should be included in each board
fact AllWindowsInEachState {
	all s: State| {
		one w: WZero| w in s.windows
		one w: WOne| w in s.windows
		one w: WTwo| w in s.windows
		one w:WThree| w in s.windows
		one w:WFour| w in s.windows
		one w:WFive| w in s.windows
		one w:WSix| w in s.windows
		one w:WSeven| w in s.windows
		one w:WEight| w in s.windows
	}  
}

/*fact AllNumbersInOneWindow {
	all n: Number| one w: Window| n in w.item
}*/

// All numbers and positions should be assoiated with a board.
// For example, since each board has 9 positions, if we have one state, we can't have 10 positions.
fact NoExtraNumbersOrWindows {
	all w: Window| w in State.windows
	all n: Number| n in State.windows.item
}

// Show the solve state of the board. This can be used as a sanity check about the board
// relationships
/* * 1 2
*  3 4 5
*  6 7 8
*/
pred solvedBoard {
	some s: State| {
		one n: One, w: s.windows & WOne| n = w.item
		one n: Two, w: s.windows & WTwo| n = w.item
		one n: Three, w: s.windows & WThree| n = w.item
		one n: Four, w: s.windows & WFour| n = w.item
		one n: Five, w: s.windows & WFive| n = w.item
		one n: Six, w: s.windows & WSix| n = w.item
		one n: Seven, w: s.windows & WSeven| n = w.item
		one n: Eight, w: s.windows & WEight| n = w.item
	}
	#State = 1
}

run solvedBoard for 9 but 1 State

// The dynamic parts...

// This predicate determines how the next board in a sequence of moves (states) can be
// as a result of the previous board
pred movePiece[board, board': set Window] {
	// TODO
	/*one w: board.windows - board.windows.item.parent| {
		all w': board' - w - w.neighbor| w'.item in dom[w.item]
		one w': w.neighbor| #w'.item = 0 and w'
	}*/
}

// This example should show a sequence of states from the initial board
/* 1 * 2      * 1 2
*  3 4 5 -> 3 4 5
*  6 7 8      6 7 8
*/
pred smallExample {
	some s: State| {
		one n: One, w: s.windows & WZero| n = w.item
		one n: Two, w: s.windows & WTwo| n = w.item
		one n: Three, w: s.windows & WThree| n = w.item
		one n: Four, w: s.windows & WFour| n = w.item
		one n: Five, w: s.windows & WFive| n = w.item
		one n: Six, w: s.windows & WSix| n = w.item
		one n: Seven, w: s.windows & WSeven| n = w.item
		one n: Eight, w: s.windows & WEight| n = w.item
	}
	some s: State| {
		one n: One, w: s.windows & WOne| n = w.item
		one n: Two, w: s.windows & WTwo| n = w.item
		one n: Three, w: s.windows & WThree| n = w.item
		one n: Four, w: s.windows & WFour| n = w.item
		one n: Five, w: s.windows & WFive| n = w.item
		one n: Six, w: s.windows & WSix| n = w.item
		one n: Seven, w: s.windows & WSeven| n = w.item
		one n: Eight, w: s.windows & WEight| n = w.item
	}
}

// TODO This will not find an instance until the dynamic logic is implemented
run smallExample for 18 but 2 State
