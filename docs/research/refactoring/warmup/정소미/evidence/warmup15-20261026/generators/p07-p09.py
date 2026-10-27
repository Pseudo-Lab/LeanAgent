"""Reproduce recorded local transformations from a frozen starting-selection snapshot.

Existing candidate bytes must match; this script does not overwrite a changed file.
"""
from pathlib import Path
import argparse, hashlib, json
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--baseline',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args();OUT=args.output
snapshot=json.loads(args.baseline.read_text());current={}
for pid in [7,8,9]:
 problem=next(p for p in snapshot['problems'] if p['id']==pid)
 candidate=next(c for c in problem['teamResults'] if c['id']==problem['selectedCandidateId'])
 code=candidate['proof']
 assert hashlib.sha256(code.encode()).hexdigest()==problem['candidateHash']
 current[pid]=code
 (OUT/f'P{pid:02}').mkdir(parents=True,exist_ok=True)
 path=OUT/f'P{pid:02}'/'current.lean'
 if path.exists():assert path.read_text()==code,f'Changed frozen starting proof: {path}'
 else:path.write_text(code)
items=[]
def put(pid,name,code,method):
 path=OUT/f'P{pid:02}'/f'{name}.lean'
 if path.exists():assert path.read_text()==code, f'Changed candidate: {path}'
 else:path.write_text(code)
 items.append({'problemId':pid,'candidate':name,'method':method,'candidateSha256':hashlib.sha256(code.encode()).hexdigest(),'proofPath':str(path.relative_to(OUT))})
def replace(s,old,new):
 assert old in s,old
 return s.replace(old,new)
s=current[7]
a='''    rcases ih rfl with v | ⟨_, h⟩ <;>
      solve_by_elim [Or.inl, Or.inr, Exists.intro, Value.inl, Value.inr, Red.inl, Red.inr]'''
direct='''    rcases ih rfl with v | ⟨_, h⟩
    · left; constructor; exact v
    · right; exact ⟨_, by constructor; exact h⟩'''
small='''    rcases ih rfl with v | ⟨_, h⟩ <;>
      first | left; constructor; assumption | right; constructor; constructor; assumption'''
put(7,'01-injection-constructors',replace(s,a,direct),'Direct Value/Red witnesses for injection cases')
put(7,'02-injection-backtracking',replace(s,a,small),'Constructor-only branch selection for injection cases')
put(7,'03-lc-have',replace(replace(s,'let lc := der.wf.2.1','have lc := der.wf.2.1'),'case var mem => simp at mem','case var mem => cases mem'),'Change closure sharing and impossible-variable elimination')
put(7,'04-var-contradiction',replace(s,'case var mem => simp at mem','case var => contradiction'),'Close impossible variable case with contradiction')
put(7,'05-injection-anonymous',replace(s,a,'''    rcases ih rfl with v | ⟨_, h⟩
    · exact .inl ⟨v⟩
    · exact .inr ⟨_, ⟨h⟩⟩'''),'Anonymous direct constructor witnesses')
put(7,'06-case-constructors',replace(replace(s,a,small),'all_goals apply_rules [Exists.intro, Term.Red.case_inl, Term.Red.case_inr]','all_goals exact ⟨_, by constructor <;> assumption⟩'),'Compose injection improvement with direct sum-case constructors')
put(7,'07-injection-and-var',replace(replace(s,a,small),'case var mem => simp at mem','case var => contradiction'),'Compose two observed improvements: injection constructors and impossible-variable closure')
s=current[8];a='''    first
    | exact ⟨_, hj, .red_S ..⟩
    | exact ⟨_, .red_S .., hj⟩'''
put(8,'01-shared-s-join',replace(s,a,'    refine ⟨_, ?_, ?_⟩ <;> first | exact hj | constructor'),'Shared S-branch join, inferred constructors')
put(8,'02-shared-s-exact',replace(s,a,'    refine ⟨_, ?_, ?_⟩ <;> first | exact hj | exact .red_S ..'),'Shared S-branch join, explicit S constructor')
put(8,'03-par-witness-let',replace(s,"    rcases iha ha'', ihb hb'' with ⟨⟨_, ha⟩, ⟨_, hb⟩⟩","    obtain ⟨_, ha⟩ := iha ha''\n    obtain ⟨_, hb⟩ := ihb hb''"),'Separate the two parallel join witness decompositions')
r=replace(replace(replace(s,'induction h₁ generalizing a₂','cases h₁'),"case' par.par iha ihb _ _ ha'' hb'' =>","case' par.par ha' hb' _ _ ha'' hb'' =>"),"iha ha'', ihb hb''","parallelReduction_diamond ha' ha'', parallelReduction_diamond hb' hb''")
put(8,'04-recursive-join',r,'Recursive common-join construction instead of induction hypotheses')
put(8,'05-shared-witness-repair',replace(s,a,'    first | refine ⟨_, hj, ?_⟩ | refine ⟨_, ?_, hj⟩\n    all_goals constructor'),'Repair unsolved witness by filling one known join component first')
s=current[9];head=s[:s.index(':= by')+len(':= by')]
put(9,'01-separate-obligations',head+'''
  intro h
  exists ChoiceBisim, ChoiceBisim.choice h
  rintro _ _ (h | h) μ <;> apply (Bisimilarity.isBisimulation _ _ h μ).imp <;> intro f s t
  all_goals first
  | exact (f _ t).imp fun _ => And.imp id ChoiceBisim.bisim
  | cases t <;> first
    | exact (f _ ‹_›).imp fun _ => And.imp Tr.choiceL ChoiceBisim.bisim
    | exact ⟨s, Tr.choiceR ‹_›, ChoiceBisim.bisim (HomBisimilarity.refl _)⟩
''','Close pure bisimulation obligations before splitting choice transitions')
r=head+'''
  intro h
  exists ChoiceBisim, ChoiceBisim.choice h
  rintro _ _ (h | h) μ
  · apply (Bisimilarity.isBisimulation _ _ h μ).imp <;> intro f s t
    cases t <;> first
    | exact (f _ ‹_›).imp fun _ => And.imp Tr.choiceL ChoiceBisim.bisim
    | exact ⟨s, Tr.choiceR ‹_›, ChoiceBisim.bisim (HomBisimilarity.refl _)⟩
  · apply (Bisimilarity.isBisimulation _ _ h μ).imp <;> intro f s t
    exact (f _ t).imp fun _ => And.imp id ChoiceBisim.bisim
'''
put(9,'02-explicit-case',r,'Separate ChoiceBisim constructors explicitly')
put(9,'03-map-pairs',replace(s,'And.imp (by first | exact id | exact Tr.choiceL) ChoiceBisim.bisim','fun ⟨ht, hb⟩ => ⟨by first | exact ht | exact Tr.choiceL ht, ChoiceBisim.bisim hb⟩'),'Construct transition/relation pair directly')
put(9,'04-explicit-case-repair',r.replace('    cases t <;> first','    all_goals cases t <;> first').replace('    exact (f _ t).imp','    all_goals exact (f _ t).imp'),'Repair actual unsolved second-direction obligations')
put(9,'05-separate-dot-constructors',replace(s,"""    repeat' first
    | exact (f _ ‹_›).imp fun _ => And.imp (by first | exact id | exact Tr.choiceL) ChoiceBisim.bisim
    | exact ⟨s, Tr.choiceR ‹_›, ChoiceBisim.bisim (HomBisimilarity.refl _)⟩
    | cases t""",'''    first
    | exact (f _ t).imp fun _ => And.imp id ChoiceBisim.bisim
    | cases t <;> first
      | exact (f _ ‹_›).imp fun _ => And.imp Tr.choiceL ChoiceBisim.bisim
      | exact ⟨_, Tr.choiceR ‹_›, .bisim (.refl _)⟩'''),'Separated obligations with inferred relation constructors')
dot=replace(replace(s,'ChoiceBisim.bisim','.bisim'),'HomBisimilarity.refl _','.refl _')
put(9,'06-expected-relation-witnesses',dot,'Use expected types for relation and reflexivity witnesses while retaining the existing branch structure')
put(9,'07-refine-imp',replace(s,'apply (Bisimilarity.isBisimulation _ _ h μ).imp','refine (Bisimilarity.isBisimulation _ _ h μ).imp ?_ ?_'),'Provide both implication holes explicitly instead of apply')
put(9,'08-bounded-branches',replace(s,"repeat' first",'iterate 2 all_goals first'),'Bound branch expansion to the two stages needed by choice transitions')
put(9,'09-named-successor',replace(s,'(f _ ‹_›)','(f s ‹_›)'),'Reuse the already bound successor instead of asking elaboration to infer it')
put(9,'10-witness-and-successor',replace(dot,'(f _ ‹_›)','(f s ‹_›)'),'Combine expected relation witnesses with the named successor')
(OUT/'candidate-plan.json').write_text(json.dumps({'scope':'Actual P07–P09 execution in frozen whole source context; no dashboard work.','paperMethods':'Partial applications of structural and constructor reasoning, not whole-paper algorithm reproductions.','candidates':items},ensure_ascii=False,indent=2)+'\n')
print(f'Exact candidate reproduction: {len(items)} files matched')
