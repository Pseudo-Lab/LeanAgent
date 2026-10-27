theorem bisimilarity_congr_choice :
    (p ~[lts (defs := defs)] q) → (choice p r) ~[lts (defs := defs)] (choice q r) := by
  intro h
  exists ChoiceBisim, ChoiceBisim.choice h
  rintro _ _ (h | h) μ <;> apply (Bisimilarity.isBisimulation _ _ h μ).imp <;> intro f s t <;>
    repeat' first
    | exact (f _ ‹_›).imp fun _ => And.imp (by first | exact id | exact Tr.choiceL) ChoiceBisim.bisim
    | exact ⟨s, Tr.choiceR ‹_›, ChoiceBisim.bisim (HomBisimilarity.refl _)⟩
    | cases t
