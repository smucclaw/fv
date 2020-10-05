
/* -------------------------------------------------------------------------- */
/* Signatures                                 */
/* -------------------------------------------------------------------------- */

sig Residence {}
sig Person {
	res : some Residence, // person takes residence in a place; each person has at least one res.
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


// if the parents have the right to care, the child has exactly the same residences as the parents
fact parent_residences_are_child_residences {
	all c: Child,  p: Parent | is_parent_of[p, c] => c in p.rc =>  p.res  = c.res
}


// TODO: investigate variants, such as: 
// the child shares some of the residences of the parents but not all


/* -------------------------------------------------------------------------- */
/* Predicates to check                         */
/* -------------------------------------------------------------------------- */

// The child lives in different residences than its parents
pred child_not_in_parent_residence [c: Child] {
	c.res & c.parents.res = none
}
run child_not_in_parent_residence
// Predicate is consistent:


// The child lives in different residences than its parents 
// but the parents have the right to care for the child 
pred child_not_in_parent_residence_with_rc [c: Child] {
	c.res & c.parents.res = none 
	&& c in c.parents.rc
}
// run child_not_in_parent_residence_with_rc
// Predicate may be inconsistent


// unexpected consequence: if the two parents have the right to care, they share the same residences
assert parents_living_together {
	all c: Child, p1: Parent, p2: Parent | 
	is_parent_of[p1, c] && is_parent_of[p2, c] && c in p1.rc && c in p2.rc
	=> p1.res = p2.res
}
// check parents_living_together
// No counterexample found. Assertion may be valid.

