/*
*	Swipe Puzzle Solver
*
*	http://jamie-wong.com/2011/10/16/fifteen-puzzle-algorithm/
*	
*	Linkteki oyunun çözümünü, istenilen state sayısında bulur.
*/

open util/ordering[State] as states

one sig Puzzle {
	empty: one Block
}

sig State {
	blocks: set Block,
	on: Block lone -> one Place
}

abstract sig Place {
	right: lone Place,
	left: lone Place,
	up: lone Place,
	down: lone Place
}

abstract sig Block {}

one sig P1, P2, P3, P4 extends Place {}

one sig B1, B2, B3, B4 extends Block {}

fact {
	states/first.blocks = Block
}

fact swipe_one_block {
	all s: State, s': states/next[s] {
		s'.blocks = s.blocks
		one b: s.blocks {
			Puzzle.empty in b.(s.on).left.~(s.on) + b.(s.on).right.~(s.on) + b.(s.on).up.~(s.on) + b.(s.on).down.~(s.on)
			Puzzle.empty.(s'.on) = b.(s.on)
			b.(s'.on) = Puzzle.empty.(s.on)
		}
	}
}

// Aşağıdakileri istediğiniz gibi düzenleyin. Bu 2x2'lik bir örnektir.
fact init_places {
	no P1.left && no P1.up && P1.right = P2 && P1.down = P3
	no P2.right && no P2.up && P2.left = P1 && P2.down = P4
	no P3.left && no P3.down && P3.right = P4 && P3.up = P1
	no P4.right && no P4.down && P4.left = P3 && P4.up = P2
}

fact game_finished_on_some_state {
	some s: State {
		B1.(s.on) = P1
		B2.(s.on) = P2
		B3.(s.on) = P3
		B4.(s.on) = P4

		states/gte[s, states/first]
	}
}

pred example {

	Puzzle.empty = B4

	let s = states/first {
		B1.(s.on) = P2
		B2.(s.on) = P4
		B3.(s.on) = P1
		B4.(s.on) = P3
	}
}


run example for exactly 4 Block, 4 Place, 4 State




