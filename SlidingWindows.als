// Needed to create an ordering of states, from initial to the solution state
open util/ordering[State] as ord

open util/integer

// An instance of the game board's state
sig State {
	windows: set Window,
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
	neighbor: some Window,
	item: one Int,
	posRow: one Int,
	posCol: one Int
}

fact NeighborIsReflexive {
	neighbor = ~neighbor
}

fact NeighborsAreSomething {
	// Windows that are next to each other are neighbors
	// (-1 + 1) doesn't mean what it looks like
	all s: State| all disj x,y: s.windows| {
		(x.posRow = y.posRow and x.posCol fun/sub y.posCol in (-1 + 1)) implies (x -> y) in neighbor
		(x.posCol = y.posCol and x.posRow fun/sub y.posRow in (-1 + 1)) implies (x -> y) in neighbor
	}

	all w: Window| (w.posRow in (1 + GameBoard.row) and w.posCol in (1 + GameBoard.column)) implies #w.neighbor = 2
	all w: Window| ((w.posRow in (1 + GameBoard.row) and not w.posCol in (1 + GameBoard.column)) or  (not w.posRow in (1 + GameBoard.row) and w.posCol in (1 + GameBoard.column))) implies #w.neighbor = 3
	all w: Window| (not w.posRow in (1 + GameBoard.row) and not w.posCol in (1 + GameBoard.column)) implies #w.neighbor = 4

	// Windows on different boards are not neighbors
	all disj s, s': State| no x: s.windows, y: s'.windows| (x -> y) in neighbor
}

fact WindowsHaveUniquePositionInBoard {
	all s: State| all disj x, y: s.windows| x.posRow != y.posRow or x.posCol != y.posCol
}

// TODO: Check if this is an actual optimization
// Because all tiles have values, this is that same as checking #s.windows.item.value, but this saves a level of indirection
fact AllNumbersOnEachBoard {
	all s: State| #s.windows.item = GameBoard.row fun/mul GameBoard.column
}

fact AllWindowsOnEachBoard {
	all s: State| #s.windows = GameBoard.row fun/mul GameBoard.column
}

fact AllWindowsValidPosition {
	all w: Window| w.posRow > 0 and w.posRow <= GameBoard.row and
								w.posCol > 0 and w.posCol <= GameBoard.column
}

fact AllNumbersInRange {
	all n: State.windows.item | n > 0 and n <= (GameBoard.row fun/mul GameBoard.column)
}

fact AllNumbersOnBoardUnique {
	all s: State| all disj w, w': s.windows | w.item != w'.item
}

// Each window is only used in one board
fact AllWindowsOnlyInOneState {
	all disj s, s': State| no w: s.windows| w in s'.windows 
}

// All numbers and positions should be assoiated with a board.
// For example, since each board has 9 positions, if we have one state, we can't have 10 positions.
fact NoExtraNumbersOrWindows {
	all w: Window| w in State.windows
}

fact EmptyRowAndColumn {
	all s: State| one w: s.windows| {
		w.item = GameBoard.row fun/mul GameBoard.column
		s.emptyRow = w.posRow and s.emptyColumn = w.posCol
	}
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
		w.item = ((w.posRow fun/sub 1) fun/mul GameBoard.column) fun/add w.posCol
	}

	GameBoard.column = 3
	GameBoard.row = 3
	#State = 1
}

run solvedBoard for 9 but 1 State, 5 int

// The dynamic parts...

// This predicate determines how the next board in a sequence of moves (states) can be
// as a result of the previous board
pred movePiece[board, board': State] {
	// w is the empty window in board
	one w: board.windows| {
		// w is the empty tile
		w.item = GameBoard.row fun/mul GameBoard.column
		// x is one of the empty tiles neighbors
		one x: w.neighbor, x': board'.windows| {
			// In the next board, the tile x becomes empty (tile is slid to replace the previously empty window)
			x'.posRow = x.posRow and x'.posCol = x.posCol and x'.item = none
			// All tiles except the empty tile and x retain their number
			// Since x is now empty, this implies that the previously empty tile must take number
			// from the x tile.
			all y: ((board.windows - w) - x)| one y': board'.windows| y'.posRow = y.posRow and y'.posCol = y.posCol and y'.item = y.item
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
	//some s: State| {
	// We could specify the initial board state here
	//}
	// solved state is solved
	some s: State| all w: s.windows {
		w.item = ((w.posRow fun/sub 1) fun/mul GameBoard.column) fun/add w.posCol
	}
	GameBoard.column = 3
	GameBoard.row = 3
	#State = 2
}

run smallExample for 18 but 2 State, 5 int
