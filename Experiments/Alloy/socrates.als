sig Being {}

sig Human in Being {}
sig God in Being {}

sig Mortal in Being {}


lone sig socrates in Human {}

lone sig zeus in God {}


fact all_humans_are_mortal {
	all h: Human | h in Mortal
}


assert socrates_is_mortal {
	socrates in Mortal
}
// check socrates_is_mortal   // accepted by Alloy
// run socrates_is_mortal   // rejected by Alloy

pred socrates_is_mortal_pred {
	socrates in Mortal
}
// run socrates_is_mortal_pred  // accepted by Alloy
// check socrates_is_mortal_pred // rejected by Alloy


// when declaring the following as a fact instead of as an assert,
// the statement zeus_is_mortal becomes derivable.
assert zeus_is_human  {
	zeus in Human
}

assert zeus_is_mortal {
	zeus in Mortal
}
//check zeus_is_mortal
