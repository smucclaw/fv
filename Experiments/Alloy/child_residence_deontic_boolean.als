/*
This is an attempt to code obligations by a boolean condition: 
Oblig(prop) is translated to O_p => prop
with a fresh boolean O_p for each obligation, with the intended meaning:
if obligation O_p is respected, then prop holds.
*/


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


// signature of obligations, 
sig Oblig {}

lone sig Ob_rule1 extends Oblig {}
lone sig Ob_rule2 extends Oblig {}


/* -------------------------------------------------------------------------- */
/* Functions, Facts                            */
/* -------------------------------------------------------------------------- */

pred is_parent_of [p: Parent, c: Child] {
	p in c.parents
}

fact exactly_two_parents {
	all c: Child | #c.parents = 2
}

pred holds_rule1 {
	some x : Oblig | x in Ob_rule1
}

pred holds_rule2 {
	some x : Oblig | x in Ob_rule2
}

/* Rule 1: If a parent has the right to care for the child, the child is obliged to share the residences of the parent.
   * Deontic statement:
	all c: Child,  p: Parent, r: Residence | is_parent_of[p, c] => c in p.rc => Oblig(p.res = c.res)
*/

fact rule1_child_typically_shares_parent_residence {
	all c: Child,  p: Parent | is_parent_of[p, c] => c in p.rc => holds_rule1 => p.res  = c.res
}


/* Rule 2: A child may not have the same residence as a parent without the right to care.
   * Deontic statement:
	all c: Child,  p: Parent, r: Residence | is_parent_of[p, c] => not c in p.rc => r in p.res => not Perm(r in c.res)
    equivalent to:
	all c: Child,  p: Parent, r: Residence | is_parent_of[p, c] => not c in p.rc => r in p.res => Oblig(not (r in c.res))
*/

fact rule2_residence_forbidden_if_no_right_to_care {
	all c: Child,  p: Parent, r: Residence | is_parent_of[p, c] => not c in p.rc => r in p.res => holds_rule2 => not (r in c.res)
}

/* -------------------------------------------------------------------------- */
/* Predicates to check                         */
/* -------------------------------------------------------------------------- */



// The child lives in different residences than its parents
pred child_not_in_parent_residence [c: Child] {
	holds_rule1 && holds_rule2 && 
	c.res & c.parents.res = none
}
// run child_not_in_parent_residence
// Predicate is consistent:



// The child lives in different residences than its parents 
// but the parents have the right to care for the child 
pred child_not_in_parent_residence_with_rc [c: Child] {
	// holds_rule1 && holds_rule2 && 
	c.res & c.parents.res = none 
	&& c in c.parents.rc
}
// run child_not_in_parent_residence_with_rc
// Predicate may be inconsistent  (if the two rules are required to hold)
// Predicate is consistent (if rule1 is invalidated)


// The child lives in the same residence as a parent
// who does not have the right to care for the child 
pred child_in_parent_residence_without_rc [c: Child] {
	// holds_rule1 && holds_rule2 && 
	(some r : Residence | r in c.res && r in c.parents.res)
	&& not c in c.parents.rc
}
run child_in_parent_residence_without_rc
// Predicate may be inconsistent  (if the two rules are required to hold)
// Predicate is consistent (if rule2 is invalidated)


