// Needed to create an ordering of states, from initial to the solution state
open util/ordering[State] as ord

// An instance of the game board's state
sig State {
	windows: set Window,
	wzero: one WZero,
	wone: one WOne,
	wtwo: one WTwo,
	wthree: one WThree,
	wfour: one WFour,
	wfive: one WFive,
	wsix: one WSix,
	wseven: one WSeven,
	weight: one WEight
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
	parent: some Window
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
			s.wzero = w
			#w.neighbor = 2
			one a: s.windows & WOne| a in w.neighbor
			one b: s.windows & WThree| b in w.neighbor
		}
		one w: s.windows & WOne| {
			s.wone = w
			#w.neighbor = 3
			one a: s.windows & WZero| a in w.neighbor
			one b: s.windows & WTwo| b in w.neighbor
			one c: s.windows & WFour| c in w.neighbor
		}
		one w: s.windows & WTwo| {
			s.wtwo = w
			#w.neighbor = 2
			one a: s.windows & WOne| a in w.neighbor
			one b: s.windows & WFive| b in w.neighbor
		}
		one w: s.windows & WThree| {
			s.wthree = w
			#w.neighbor = 3
			one a: s.windows & WZero| a in w.neighbor
			one b: s.windows & WFour| b in w.neighbor
			one c: s.windows & WSix| c in w.neighbor
		}
		one w: s.windows & WFour| {
			s.wfour = w
			#w.neighbor = 4
			one a: s.windows & WOne| a in w.neighbor
			one b: s.windows & WThree| b in w.neighbor
			one c: s.windows & WFive| c in w.neighbor
			one d: s.windows & WSeven| d in w.neighbor
		}
		one w: s.windows & WFive| {
			s.wfive = w
			#w.neighbor = 3
			one a: s.windows & WTwo| a in w.neighbor
			one b: s.windows & WFour| b in w.neighbor
			one c: s.windows & WEight| c in w.neighbor
		}
		one w: s.windows & WSix| {
			s.wsix = w
			#w.neighbor = 2
			one a: s.windows & WThree| a in w.neighbor
			one b: s.windows & WSeven| b in w.neighbor
		}
		one w: s.windows & WSeven| {
			s.wseven = w
			#w.neighbor = 3
			one a: s.windows & WSix| a in w.neighbor
			one b: s.windows & WFour| b in w.neighbor
			one c: s.windows & WEight| c in w.neighbor
		}
		one w: s.windows & WEight| {
			s.weight = w
			#w.neighbor = 2
			one a: s.windows & WSeven| a in w.neighbor
			one b: s.windows & WFive| b in w.neighbor
		}
	}
}

// Each game board should include every number and only once
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

// Each board position should be included in each board and only once
// I think this is implied by WindowGraph
/*fact AllWindowsInEachState {
	all s: State| {
		one w: WZero| w in s.windows
		one w: WOne| w in s.windows
		one w: WTwo| w in s.windows
		one w: WThree| w in s.windows
		one w: WFour| w in s.windows
		one w: WFive| w in s.windows
		one w: WSix| w in s.windows
		one w: WSeven| w in s.windows
		one w: WEight| w in s.windows
	}  
}*/

// Each window is only used in one board
fact AllWindowsOnlyInOneState {
	all disj s, s': State| no w: s.windows| w in s'.windows 
}

// A number can't be in two different positions on the same board
fact AllNumbersInOneWindowPerState {
	all n: Number, s: State| one w: s.windows| n = w.item
}

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
}

run solvedBoard for 9 but 1 State

// The dynamic parts...

// This predicate determines how the next board in a sequence of moves (states) can be
// as a result of the previous board
pred movePiece[board, board': State] {
	// w is the empty window in board
	one w: board.windows - board.windows.item.parent| {
		// x is one of the empty tiles neighbors
		one x: w.neighbor| {
			// In the next board, the tile x becomes empty (tile is slid to replace the previously empty window)
			(x in WZero implies none = board'.wzero.item) and
			(x in WOne implies none = board'.wone.item) and
			(x in WTwo implies none = board'.wtwo.item) and
			(x in WThree implies none = board'.wthree.item) and
			(x in WFour implies none = board'.wfour.item) and
			(x in WFive implies none = board'.wfive.item) and
			(x in WSix implies none = board'.wsix.item) and
			(x in WSeven implies none = board'.wseven.item) and
			(x in WEight implies none = board'.weight.item) and
			// All tiles except the empty tile and x retain their number
			// Since x is now empty, this implies that the previously empty tile must take number
			// from the x tile.
			all y: ((board.windows - w) - x)| (y in WZero implies y.item = board'.wzero.item) and
																	 (y in WOne implies y.item = board'.wone.item) and
																	 (y in WTwo implies y.item = board'.wtwo.item) and
																	 (y in WThree implies y.item = board'.wthree.item) and
																	 (y in WFour implies y.item = board'.wfour.item) and
																	 (y in WFive implies y.item = board'.wfive.item) and
																	 (y in WSix implies y.item = board'.wsix.item) and
																	 (y in WSeven implies y.item = board'.wseven.item) and
																	 (y in WEight implies y.item = board'.weight.item)
		}
	}
}

fact stateTransition {
  all s: State, s': ord/next[s] {
      movePiece[s, s']
  }
}

// This example should show a sequence of states from the initial board
/* 1 2 5    * 1 2
*  3 4 * -> 3 4 5
*  6 7 8    6 7 8
*/
pred smallExample {
	// Initial state is the following "initial" state
	some s: State| {
		one w: s.windows & WZero| One = w.item
		one w: s.windows & WOne| Two = w.item
		one w: s.windows & WTwo| Five = w.item
		one w: s.windows & WThree| Three = w.item
		one w: s.windows & WFour| Four = w.item
		one w: s.windows & WFive| none = w.item
		one w: s.windows & WSix| Six = w.item
		one w: s.windows & WSeven| Seven = w.item
		one w: s.windows & WEight| Eight = w.item
	}
	// solved state is solved
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

run smallExample for 36 but 4 State
