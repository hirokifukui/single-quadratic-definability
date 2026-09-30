import MPUP.WeightedBound

-- Statement-fidelity gate: does `wtCount` compute the weighted monomial count the paper means?
-- Cross-checked against an independent Python enumeration.  The two closed forms are no longer
-- asserted here in prose: they are the theorems `MPUP.monoCount_closed_form` and
-- `MPUP.wtCount_closed_form` in MPUP/WeightedBound.lean, proved s34.

#eval (List.range 5).map (fun d => (List.range 4).map (fun k => MPUP.monoCount d k))
#eval (List.range 5).map (fun d => (List.range 4).map (fun k => MPUP.wtCount d k))

-- degenerate controls
#eval MPUP.wtCount 0 3   -- expect 0: no degree is left over at d = 0
#eval MPUP.wtCount 3 0   -- expect 3: one empty monomial, weight 3
#eval MPUP.monoCount 3 0 -- expect 1
