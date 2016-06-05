// Needed to create an ordering of states, from initial to the solution state
open util/ordering[State] as ord

// An instance of the game board's state
sig State {
	windows: set Windows,
	emptyRow: one Int,
	emptyColumn: one Int
}

one sig GameBoard {
	column: one Int, 
	row: one Int
}

// Gameboard functions
//fun createTiles[n, m: int]: set Number {}

// A position on the board
sig Window {
	item: lone Int,
	posRow: one Int,
	posCol: one Int
}

fact WindowsHaveUniquePositionInBoard {
	all s: State| all disj x, y: s.windows| x.posRow != y.posRow or x.posCol != y.posCol
}

fact AllNumbersOnEachBoard {
	all s: State| #s.windows.item = ((GameBoard.row fun/mult GameBoard.column) fun/sub 1)
}

fact AllWindowsOnEachBoard {
	all s: State| #s.windows = GameBoard.row fun/mult GameBoard.column
}

fact AllWindowsValidPosition {
	all w: Window| w.posRow > 0 and w.posRow <= GameBoard.row and
								w.posCol > 0 and w.posCol <= GameBoard.column
}

fact AllNumbersInRange {
	all n: State.windows.item| n > 0 and n < (GameBoard.row fun/mult GameBoard.column)
}

fact AllNumbersOnBoardUnique {
	all s: State| all disj n, n': State.windows.item| n != n'
}

// The positions on the board can be thought of as a graph. The vertices are the positions on the board
// and the edges are the neighboring relationships between positions.
// Each state (instance of a game board) needs its own graph
// This graph is no longer a part of the metamodel
pred WindowGraphPred[state: State] {
	
	all w: state.windows| {
			
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
	// solved state is solved
	one s: State| all w: s.windows {
		w.item = ((w.posRow fun/sub 1) fun/mult GameBoard.column) + w.posCol
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
	some s: State| all w: s.windows {
		w.item = ((w.posRow fun/sub 1) fun/mult GameBoard.column) + w.posCol
	}
}

run smallExample for 36 but 4 State
