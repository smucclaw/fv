/*
This is an attempt to code obligations by a reduction to alethic modal logic 
(Andersonian-Kangerian Reduction), as suggested in 

https://plato.stanford.edu/entries/logic-deontic/#3

and then reducing alethic modal logic to a possible-world semantics. 
The coding below is not complete yet (the constant d of the reduction is not taken into account)
but even without that, there is an unfortunate interaction with quantification and the worlds 
(see more detailed discussion below).

This approach is therefore unlikely to succeed.
*/



/* -------------------------------------------------------------------------- */
/* Signatures                                 */
/* -------------------------------------------------------------------------- */

sig World {
	acc: set World      // accessibility relation from this to deontically preferred worlds.
}

sig Residence {}
sig Person {
	res : World -> some Residence, // person takes residence in a place; each person has at least one res.
}


// note: the two 'extends' declarations make Child and Parent two disjoint subsets of Person
sig Child extends Person {
	parents : set Parent
}

sig Parent extends Person {
	rc : set Child,  // parent has right to care for children
}


/* -------------------------------------------------------------------------- */
/* Functions, Facts                            */
/* -------------------------------------------------------------------------- */

pred is_parent_of [p: Parent, c: Child] {
	p in c.parents
}

fact exactly_two_parents {
	all c: Child | #c.parents = 2
}


/* A child may not have the same residence as a parent without the right to care.
   * Deontic statement:
	all c: Child,  p: Parent, r: Residence | is_parent_of[p, c] => not c in p.rc => r in p.res => not Perm(r in c.res)
*/


fact residence_forbidden_if_no_right_to_care {
	all c: Child,  p: Parent, r: Residence, w1: World | is_parent_of[p, c] => not c in p.rc => 
	 (w1 -> r) in p.res => not some w2: World | w2 in w1.acc && (w2 -> r) in c.res
}

/*
Comment on this formalization: it is an attempt to be a direct translation of deontic primitives into a possible-world semantics.
The world w1 is the current world, w2 is the "ideal" world with w2 in w1.acc.
The generated model has (for p0 not having right to care of c):
-  (w1, r0) : p0.res and indeed, one does not have (w2, r0) : p0.res
-  (w2, r1) : p0.res and(w2, r1) : c, but there is no world accessible from w2. 
All this indicates an unsound interaction between quantifiers which could maybe be avoided by rewriting
r in p.res => not Perm(r in c.res)
to
not Perm(r in p.res => r in c.res)
*/

/* A child allowed to live in the same residence as a parent is required to live there.
   * Deontic statement:
	all c: Child,  p: Parent, r: Residence | is_parent_of[p, c] => r in p.res => Perm(r in c.res) => O(r in c.res)
*/

fact in_parent_residence_if_possible {
	all c: Child,  p: Parent, r: Residence | is_parent_of[p, c] =>
	(all w1: World | (w1 -> r) in p.res =>
		(some w2: World | w2 in w1.acc && (w2 -> r) in c.res) => (all w2: World | w2 in w1.acc => (w2 -> r) in c.res))
}

/* -------------------------------------------------------------------------- */
/* Predicates to check                         */
/* -------------------------------------------------------------------------- */

pred child_illegally_in_res_parent_no_rc[c: Child, w1, w2: World] {
	one r: Residence | one p: Parent | w2 in w1.acc && (w2 -> r) in c.res && (w2 -> r) in p.res && not c in p.rc
}
run child_illegally_in_res_parent_no_rc  for exactly 1 Child,  2 World, 2 Residence, 3 Person
