sig State {
	windows: set Window
}

abstract sig Window {
	item: lone Number,
	neighbor: set Window
}
sig WZero, WOne, WTwo, WThree, WFour, WFive, WSix, WSeven, WEight extends Window {}

abstract sig Number {}
sig One, Two, Three, Four, Five, Six, Seven, Eight extends Number {}


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

fact AllNumbersInOneWindow {
	all n: Number| one w: Window| n in w.item
}

fact NoExtraNumbersOrWindows {
	all w: Window| w in State.windows
	all n: Number| n in State.windows.item
}

pred show {
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

run show for 9 but 2 State
