// Needed to create an ordering of states, from initial to the solution state
open util/ordering[State] as ord

// Seems to be needed for multiplication function
open util/integer

// An instance of the game board's state
sig State {}
// Singleton. Holds the dimensions of the board.
one sig GameBoard {
	column: one Int, 
	row: one Int
}

// A position on the board
sig Window {
	neighbor: some Window,
	item: State -> one Int,
	posRow: one Int,
	posCol: one Int
}

fun getItem[w: Window, s: State]: set Int {
	w.item[s]
}

fun numRow[]: one Int {
	GameBoard.row
}

fun numCol[]: one Int {
	GameBoard.column
}

fact NeighborsDefinition {
	// Windows that are next to each other are neighbors
	// (-1 + 1) doesn't mean what it looks like. Remember + means set union.
	all disj x,y: Window| {
		(x.posRow = y.posRow and x.posCol fun/sub y.posCol in (-1 + 1)) implies (x -> y) in neighbor
		(x.posCol = y.posCol and x.posRow fun/sub y.posRow in (-1 + 1)) implies (x -> y) in neighbor
	}

	// (1 + numRow) doesn't mean what it looks like. Remember + means set union.
	// Corner windows have 2 neighbors
	all w: Window| (w.posRow in (1 + numRow) and w.posCol in (1 + numCol)) implies #w.neighbor = 2
	// Edge windows that are not corners have 3 neighbors
	all w: Window| ((w.posRow in (1 + numRow) and not w.posCol in (1 + numCol)) or  (not w.posRow in (1 + numRow) and w.posCol in (1 + numCol))) implies #w.neighbor = 3
	// Interior windows have 4 neighbors
	all w: Window| (not w.posRow in (1 + numRow) and not w.posCol in (1 + numCol)) implies #w.neighbor = 4
}

fact AllWindows {
	#Window = numRow fun/mul numCol
}

fact WindowsHaveUniquePositionInBoard {
	all disj x, y: Window| x.posRow != y.posRow or x.posCol != y.posCol
}

fact AllWindowsValidPosition {
	all w: Window| {
		w.posRow > 0 and w.posRow <= numRow
	 	w.posCol > 0 and w.posCol <= numCol
	}
}

fact AllNumbersInEachState {
	all s: State| #getItem[Window, s] = numRow fun/mul numCol
}

fact AllNumbersInRange {
	all s: State| all n: getItem[Window, s] | n > 0 and n <= (numRow fun/mul numCol)
}

fact AllNumbersOnBoardUnique {
	all s: State| all disj w, w': Window | getItem[w, s] != getItem[w', s]
}

// The dynamic parts...

pred LastStateIsSolved {
	one s: State| {
		s = ord/last
		all w: Window {
			getItem[w, s] = ((w.posRow fun/sub 1) fun/mul numCol) fun/add w.posCol
		}
	}	
}

// This predicate determines how the next board in a sequence of moves (states) can be
// as a result of the previous board
pred MovePiece[board, board': State] {
	// w is the empty window in board
	one w: Window| {
		// w is the empty tile
		getItem[w, board] = numRow fun/mul numCol
		// x is one of the empty tiles neighbors
		one x: w.neighbor| {
			// In the next board, the tile x becomes empty (tile is slid to replace the previously empty window)
			getItem[x, board'] = getItem[w, board]
			// All tiles except the empty tile and x retain their number
			// Since x is now empty, this implies that the previously empty tile must take number
			// from the x tile.
			all y: ((Window - w) - x)| {
				getItem[y, board'] = getItem[y, board]
			}
		}
	}
}

fact StateTransition {
  all s: State, s': ord/next[s] {
      MovePiece[s, s']
  }
}

// The definition of neighbors assumes that the board is not degenerate.
fact BoardIsNotDegenerate {
	numCol >= 2
	numRow >= 2
}

assert OneMoveValid {
	some s: State, s': ord/next[s]| one w: Window| one w': (Window - w)| {
		getItem[w, s] = getItem[w', s']
		getItem[w', s] = getItem[w, s']
	}
}

check OneMoveValid for 9 but 2 State, 5 int

assert NeighborIsReflexive {
	neighbor = ~neighbor
}

check NeighborIsReflexive for 9 Window, 2 State, 5 int

assert OneItemPerState {
	all w: Window| #w.item = #State
}

check OneItemPerState for 9 Window, 2 State, 5 int

// This example should show a sequence of states from the initial board
pred SolveProblemFromInitialState {
	// Initial state is the following "initial" state
	some s: State| {
	 	s = ord/first
	 	all w: Window {
			(w.posRow = 1 and w.posCol = 1) implies getItem[w, s] = 9 // numRow * numCol is the blank space
			(w.posRow = 1 and w.posCol = 2) implies getItem[w, s] = 1
			(w.posRow = 1 and w.posCol = 3) implies getItem[w, s] = 2
			(w.posRow = 2 and w.posCol = 1) implies getItem[w, s] = 5
			(w.posRow = 2 and w.posCol = 2) implies getItem[w, s] = 6
			(w.posRow = 2 and w.posCol = 3) implies getItem[w, s] = 3
			(w.posRow = 3 and w.posCol = 1) implies getItem[w, s] = 4
			(w.posRow = 3 and w.posCol = 2) implies getItem[w, s] = 7
			(w.posRow = 3 and w.posCol = 3) implies getItem[w, s] = 8
		}
	}

	LastStateIsSolved

	numCol = 3
	numRow = 3
}

run SolveProblemFromInitialState for 9 Window, 9 State, 5 int


// This example should show a sequence of states from any state 9 moves from the solution state.
pred SolveProblemFromRandomState {
	LastStateIsSolved

	numCol = 3
	numRow = 3
}

run SolveProblemFromRandomState for 9 Window, 9 State, 5 int
