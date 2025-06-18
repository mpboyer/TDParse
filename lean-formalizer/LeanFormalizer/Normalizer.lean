import LeanFormalizer.TypeSystem

section
open ModeLabel
variable {α α' β β' γ: Type}
variable {x : ModeLabel}

-- Before adding unit: 
--  | m:UR MR __ | m:UR DN MR __ -> Not adding void semantics
--  | m:UL ML __ | m:UL DN ML __ -> Not adding void semantics

-- Before adding DN
-- | m:DN MR DN MR __ | m:DN ML DN ML __ | m:DN ML DN MR __ 
-- -> don't mean anything -> DN AP 
-- | m:DN AP DN MR __ | m:DN ML DN AP __ -> don't bother adding things to remove then 
-- | m:DN CU __ -> why wouldn't you have done it 

-- Before adding Join
-- | m:JN MR MR __ | m:JN MR JN MR __ 
-- | m:JN ML ML __ | m:JN ML JN ML __ -> don't mean anything
-- this sequence of combinators will not add any new meaning
-- | m:JN ML MR __ | m:JN ML JN MR __ -> AP
-- | m:JN AP MR __ | m:JN AP JN MR __ -> UR
-- | m:JN ML AP __ | m:JN ML JN AP __ -> UL
-- => false

-- Before adding Join
-- | mlab => Id.run do
--  let .comp f _ := w | true
--    if not (FX.commutative f) then true else
--     match mlab with
--   | m:JN MR AP __ | m:JN AP ML __
--    | m:JN AP AP __ | m:JN AP JN AP __
--    | m:JN MR ML __ | m:JN MR JN ML __
--     => false

-- add elimination of spurious ambiguity

theorem TDParse.Unit : m:DN MR DN MR x = m:MR DN MR x := 
  sorry
