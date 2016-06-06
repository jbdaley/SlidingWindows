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

fact NeighborIsReflexive {
	neighbor = ~neighbor
}

fact NeighborsAreSomething {
	// Windows that are next to each other are neighbors
	// (-1 + 1) doesn't mean what it looks like. Remember + means set union.
	all disj x,y: Window| {
		(x.posRow = y.posRow and x.posCol fun/sub y.posCol in (-1 + 1)) implies (x -> y) in neighbor
		(x.posCol = y.posCol and x.posRow fun/sub y.posRow in (-1 + 1)) implies (x -> y) in neighbor
	}

	// (1 + GameBoard.row) doesn't mean what it looks like. Remember + means set union.
	// Corner windows have 2 neighbors
	all w: Window| (w.posRow in (1 + GameBoard.row) and w.posCol in (1 + GameBoard.column)) implies #w.neighbor = 2
	// Edge windows that are not corners have 3 neighbors
	all w: Window| ((w.posRow in (1 + GameBoard.row) and not w.posCol in (1 + GameBoard.column)) or  (not w.posRow in (1 + GameBoard.row) and w.posCol in (1 + GameBoard.column))) implies #w.neighbor = 3
	// Interior windows have 4 neighbors
	all w: Window| (not w.posRow in (1 + GameBoard.row) and not w.posCol in (1 + GameBoard.column)) implies #w.neighbor = 4
}

fact AllWindows {
	#Window = GameBoard.row fun/mul GameBoard.column
}

fact WindowsHaveUniquePositionInBoard {
	all disj x, y: Window| x.posRow != y.posRow or x.posCol != y.posCol
}

fact AllWindowsValidPosition {
	all w: Window| {
		w.posRow > 0 and w.posRow <= GameBoard.row
	 	w.posCol > 0 and w.posCol <= GameBoard.column
	}
}

fact AllNumbersInEachState {
	all s: State| #getItem[Window, s] = GameBoard.row fun/mul GameBoard.column
}

fact AllNumbersInRange {
	all s: State| all n: getItem[Window, s] | n > 0 and n <= (GameBoard.row fun/mul GameBoard.column)
}

fact AllNumbersOnBoardUnique {
	all s: State| all disj w, w': Window | getItem[w, s] != getItem[w', s]
}

fact ItemCardinality {
	all w: Window| #w.item = #State
}

pred LastStateIsSolved {
	one s: State| {
		s = ord/last
		all w: Window {
			getItem[w, s] = ((w.posRow fun/sub 1) fun/mul GameBoard.column) fun/add w.posCol
		}
	}	
}

// The dynamic parts...

// This predicate determines how the next board in a sequence of moves (states) can be
// as a result of the previous board
pred movePiece[board, board': State] {
	// w is the empty window in board
	one w: Window| {
		// w is the empty tile
		getItem[w, board] = GameBoard.row fun/mul GameBoard.column
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

fact stateTransition {
  all s: State, s': ord/next[s] {
      movePiece[s, s']
  }
}

// This example should show a sequence of states from the initial board
pred SolveProblem {
	// Initial state is the following "initial" state
	//some s: State| {
	// s = ord/first
	// We could specify the initial board state here
	//}

	LastStateIsSolved

	GameBoard.column = 3
	GameBoard.row = 3
}

run SolveProblem for 9 but 2 State, 5 int
