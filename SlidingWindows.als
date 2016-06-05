// Needed to create an ordering of states, from initial to the solution state
open util/ordering[State] as ord

open util/integer

// An instance of the game board's state
sig State {
	//windows: set Window,
	//emptyRow: one Int,
	//emptyColumn: one Int
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
	item: State -> one Int,
	posRow: one Int,
	posCol: one Int
}

fact NeighborIsReflexive {
	neighbor = ~neighbor
}

fact NeighborsAreSomething {
	// Windows that are next to each other are neighbors
	// (-1 + 1) doesn't mean what it looks like
	all disj x,y: Window| {
		(x.posRow = y.posRow and x.posCol fun/sub y.posCol in (-1 + 1)) implies (x -> y) in neighbor
		(x.posCol = y.posCol and x.posRow fun/sub y.posRow in (-1 + 1)) implies (x -> y) in neighbor
	}

	all w: Window| (w.posRow in (1 + GameBoard.row) and w.posCol in (1 + GameBoard.column)) implies #w.neighbor = 2
	all w: Window| ((w.posRow in (1 + GameBoard.row) and not w.posCol in (1 + GameBoard.column)) or  (not w.posRow in (1 + GameBoard.row) and w.posCol in (1 + GameBoard.column))) implies #w.neighbor = 3
	all w: Window| (not w.posRow in (1 + GameBoard.row) and not w.posCol in (1 + GameBoard.column)) implies #w.neighbor = 4
}

fact WindowsHaveUniquePositionInBoard {
	all disj x, y: Window| x.posRow != y.posRow or x.posCol != y.posCol
}

fact AllNumbersInEachState {
	all s: State| #(Window.item[s]) = GameBoard.row fun/mul GameBoard.column
}

fact AllWindows {
	#Window = GameBoard.row fun/mul GameBoard.column
}

fact AllWindowsValidPosition {
	all w: Window| w.posRow > 0 and w.posRow <= GameBoard.row and
								w.posCol > 0 and w.posCol <= GameBoard.column
}

fact AllNumbersInRange {
	all s: State| all n: Window.item[s] | n > 0 and n <= (GameBoard.row fun/mul GameBoard.column)
}

fact AllNumbersOnBoardUnique {
	all s: State| all disj w, w': Window | w.item[s] != w'.item[s]
}

fact ItemCardinality {
	all w: Window| #w.item = #State
}

// Show the solve state of the board. This can be used as a sanity check about the board
// relationships
/* * 1 2
*  3 4 5
*  6 7 8
*/
pred solvedBoard {
	// solved state is solved
	one s: State| all w: Window {
		w.item[s] = ((w.posRow fun/sub 1) fun/mul GameBoard.column) fun/add w.posCol
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
	one w: Window| {
		// w is the empty tile
		w.item[board] = GameBoard.row fun/mul GameBoard.column
		// x is one of the empty tiles neighbors
		one x: w.neighbor| {
			// In the next board, the tile x becomes empty (tile is slid to replace the previously empty window)
			x.item[board'] = w.item[board]
			// All tiles except the empty tile and x retain their number
			// Since x is now empty, this implies that the previously empty tile must take number
			// from the x tile.
			all y: ((Window - w) - x)| {
				y.item[board'] = y.item[board]
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
	one s: State| all w: Window {
		w.item[s] = ((w.posRow fun/sub 1) fun/mul GameBoard.column) fun/add w.posCol
	}
	GameBoard.column = 3
	GameBoard.row = 3
	#State = 2
}

run smallExample for 9 but 2 State, 5 int
