% run with:
%    eprover --auto --tptp3-format --proof-object professional_conduct_rule_34.p > professional_conduct_rule_34.out


% not modeled: (34 - 1 - e) and (34 - 1 - f)
fof(must_not_accept_34_1, axiom,
   (! [Vlpr, Vapp] :
    (pMustNotAcceptApp_34_1(Vlpr, Vapp) <=>
      ( (? [Vbsn] : (pAssociatedWith(Vapp, Vbsn) & pIncompatibleDignity(Vbsn)))
      | (? [Vbsn] : (pAssociatedWith(Vapp, Vbsn) & 
            (pInterferesWithPrimaryOccupationLawyer(Vbsn, Vlpr) |
             pInterferesWithAvailability(Vbsn, Vlpr) |
             pInterferesWithRepresentationClient(Vbsn, Vlpr))))
      | (? [Vbsn] : (pAssociatedWith(Vapp, Vbsn) & pUnfairlyAttractBusiness(Vbsn)))
      | (? [Vbsn, Vprs] : (pAssociatedWith(Vapp, Vbsn) & pPaymentOfFeeToFor(Vprs, Vbsn) & pUnauthorised(Vprs, Vbsn)))
      )
    )
   )
).

fof(must_not_accept_34_6, axiom,
   (! [Vlpr, Vapp] :
    (pMustNotAcceptApp_34_6(Vlpr, Vapp) <=>
     (pLegalPractitioner(Vlpr) & pExecutiveAppointment(Vapp) &
       (
        ~ pMayAcceptApp_34_2(Vlpr, Vapp) &
        ~ pMayAcceptApp_34_3(Vlpr, Vapp) &
        ~ pMayAcceptApp_34_4(Vlpr, Vapp) &
        ~ pMayAcceptApp_34_5(Vlpr, Vapp) 
       ) &
       (pExecAppointmentOtherSGLawPractice_34_6a(Vlpr, Vapp) |
        pExecAppointmentBSE_34_6b(Vlpr, Vapp)
       )
     )
    )
   )
).

fof(must_not_accept, axiom,
   (! [Vlpr, Vapp] :
    (pMustNotAcceptApp(Vlpr, Vapp) <=>
     (pMustNotAcceptApp_34_1(Vlpr, Vapp) |
      pMustNotAcceptApp_34_6(Vlpr, Vapp))))
).

fof(property, negated_conjecture,
    ~ (! [Vlpr, Vapp] : (pMayAcceptApp(Vlpr, Vapp) | pMustNotAcceptApp(Vlpr, Vapp)))).
