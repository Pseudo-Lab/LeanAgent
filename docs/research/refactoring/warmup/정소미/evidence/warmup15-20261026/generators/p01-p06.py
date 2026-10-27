"""Generate the exact P01–P06 experimental candidates; no Lean or network calls."""
from pathlib import Path
import argparse,hashlib,json
PROOFS={}

def variants():
 p=PROOFS[1]
 yield 1,'r1-remove-nil-rewrite',p.replace(', List.not_mem_nil','')
 yield 1,'r2-single-normalization',p.replace('  simp only [Imperative.HasVarsPure.getVars, List.mem_append, List.mem_singleton]\n','').replace('simp only [Lambda.LExpr.LExpr.getVars','simp_all only [Imperative.HasVarsPure.getVars, Lambda.LExpr.LExpr.getVars')
 p=PROOFS[2]
 yield 2,'r1-unused-intro',p.replace('rintro -','intro')
 yield 2,'r2-direct-subset-term',p.replace('  apply List.Sublist.subset\n','  refine List.Sublist.subset ?_\n')
 p=PROOFS[3]
 yield 3,'r1-direct-update-chain',p.replace('    apply updatedStatesUpdate lu\n    apply updatedStatesDefMonotone\n    exact UpdateStatesDefined\' hup','    exact updatedStatesUpdate lu (updatedStatesDefMonotone (UpdateStatesDefined\' hup))')
 p=PROOFS[4]
 yield 4,'r1-typed-continuity',p.replace("hf.inner' (𝕜 := ℝ) f (fun _ => f x) continuous_const","(show Continuous (fun y => ⟪f y, f x⟫_ℝ) from hf.inner' _ _ continuous_const)")
 yield 4,'r2-direct-trim-trans',p.replace('(integral_trim hle (hgs.continuous.mul hc).stronglyMeasurable).symm.trans\n      (by simpa only [inner_smul_right\', Pi.mul_apply] using\n        hg _ (.smul_right ⟨hgs, hgc⟩ contDiff_const))',"by\n      rw [integral_trim hle (hgs.continuous.mul hc).stronglyMeasurable]\n      simpa only [inner_smul_right', Pi.mul_apply] using\n        hg _ (.smul_right ⟨hgs, hgc⟩ contDiff_const)")
 p=PROOFS[5]
 yield 5,'r1-derive-c2-from-c3',p.replace('  have hA₂ : ContDiff ℝ 2 A := hA.of_le (by decide)\n  have hA₃ : ContDiff ℝ 3 A := hA.of_le (by decide)','  have hA₃ : ContDiff ℝ 3 A := hA.of_le (by decide)\n  have hA₂ := hA₃.of_le (show (2 : WithTop ℕ∞) ≤ 3 by decide)')
 yield 5,'r2-projections-directed-rewrite',p.replace('simp only [k, (h t _).1, div_eq_inv_mul, Space.deriv_eq_fderiv_basis, fderiv_const_mul','rw [(h t _).1]\n        simp only [k, div_eq_inv_mul, Space.deriv_eq_fderiv_basis, fderiv_const_mul')
 p=PROOFS[6]
 yield 6,'r1-finite-membership-proof',p.replace('(by simp [hφψ, hψφ])','(by simp only [List.mem_cons, List.mem_singleton, forall_eq_or_imp, crAnTimeOrderRel_refl, hφψ, hψφ, and_self, imp_self, forall_const])')
 yield 6,'r2-share-normalized-factorization',p.replace('      simp only [l, r, t, e, ofCrAnListF_append, map_mul, mul_assoc]','      simp only [l, r, t, e, ofCrAnListF_append, map_mul, mul_assoc, List.append_assoc, List.cons_append, List.nil_append]').replace('      simp only [List.append_assoc, List.cons_append, List.nil_append] at s v\n','')

def extra_variants():
 p=PROOFS[2]
 yield 2,'r3-default-local-rules',p.replace('apply_rules only [*, ', 'apply_rules [')
 p=PROOFS[3]
 a="  · apply updatedStatesUpdate lu\n    apply updatedStatesDefMonotone\n    exact UpdateStatesDefined' hup"
 b="  · exact updatedStatesUpdate lu (updatedStatesDefMonotone (UpdateStatesDefined' hup))"
 assert a in p
 yield 3,'r2-direct-update-chain-fixed-edit',p.replace(a,b)
 p=next(code for i,label,code in variants() if i==4 and label=='r2-direct-trim-trans')
 yield 4,'r3-repair-trim-direction',p.replace('rw [integral_trim hle', 'rw [← integral_trim hle')
 p=PROOFS[5]
 yield 5,'r3-shared-c3-typed-c2',p.replace('  have hA₂ : ContDiff ℝ 2 A := hA.of_le (by decide)\n  have hA₃ : ContDiff ℝ 3 A := hA.of_le (by decide)','  have hA₃ : ContDiff ℝ 3 A := hA.of_le (by decide)\n  have hA₂ : ContDiff ℝ 2 A := hA₃.of_le (by decide)')
 p=PROOFS[5]
 yield 5,'r4-delete-reported-unused-simp',p.replace('simp only [Pi.sub_apply, sub_right_inj]', 'simp only [sub_right_inj]')
 p=next(code for i,label,code in variants() if i==5 and label=='r2-projections-directed-rewrite')
 yield 5,'r5-repair-under-binder',p.replace('rw [(h t _).1]', 'simp_rw [(h t _).1]')
 p=PROOFS[6]
 yield 6,'r3-explicit-pair-condition',p.replace('(by simp [hφψ, hψφ])','(by simp only [List.forall_mem_cons, List.forall_mem_nil, crAnTimeOrderRel_refl, hφψ, hψφ, and_self])')
 p=PROOFS[6]
 yield 6,'r4-normalize-helper-contract',p.replace('(crAnTimeOrderList (x ++ z ++ y))','(crAnTimeOrderList (x ++ (z ++ y)))').replace('rw [crAnTimeOrderList, insertionSort_of_eq_list','rw [← List.append_assoc, crAnTimeOrderList, insertionSort_of_eq_list').replace('      simp only [List.append_assoc, List.cons_append, List.nil_append] at s v\n','')

def focus_variants():
 p=PROOFS[5]
 yield 5,'r6-simp-small-coefficient',p.replace('        ring1','        simp [pow_two, mul_assoc, mul_left_comm, mul_comm]')
 yield 5,'r7-restrict-final-normalization',p.replace('          simp [k, div_eq_mul_inv, pow_two,\n            mul_assoc, mul_left_comm, mul_comm]','          simp only [k, div_eq_mul_inv, pow_two, mul_inv_rev, one_mul,\n            mul_assoc, mul_left_comm, mul_comm, inv_mul_cancel_left₀ 𝓕.μ₀_ne_zero]')
 p=next(code for i,label,code in extra_variants() if i==6 and label=='r4-normalize-helper-contract')
 a='      have s := f [φ, ψ] (by simp [hφψ, hψφ])\n      have v := f [ψ, φ] (by simp [hφψ, hψφ])\n      rw [s, v, smul_sub, smul_comm]'
 b='      erw [f [φ, ψ] (by simp [hφψ, hψφ]), f [ψ, φ] (by simp [hφψ, hψφ]),\n        smul_sub, smul_comm]'
 assert a in p
 yield 6,'r5-inline-shared-helper-uses',p.replace(a,b).replace('simp only [List.append_nil, ofCrAnListF_nil','simp only [List.nil_append, ofCrAnListF_nil')
 p=PROOFS[6]
 yield 6,'r6-close-empty-predicate-directly',p.replace('(by simp [hφψ, hψφ])','(by simp only [List.forall_mem_cons, crAnTimeOrderRel_refl, hφψ, hψφ, true_and]; exact List.forall_mem_nil _)')
 p=PROOFS[5]
 p8=p.replace('          simp [k, div_eq_mul_inv, pow_two,\n            mul_assoc, mul_left_comm, mul_comm]','          simp only [k, div_eq_mul_inv, pow_two, mul_inv_rev, one_mul,\n            mul_assoc, mul_left_comm, mul_comm]\n          rw [mul_left_comm 𝓕.μ₀, mul_inv_cancel_left₀ 𝓕.μ₀_ne_zero]')
 yield 5,'r8-repair-scalar-cancellation',p8
 yield 5,'r9-combine-verified-pruning',p8.replace('simp only [Pi.sub_apply, sub_right_inj]', 'simp only [sub_right_inj]')

def main():
 parser=argparse.ArgumentParser(description=__doc__)
 parser.add_argument('--baseline',type=Path,required=True)
 parser.add_argument('--output',type=Path,required=True)
 args=parser.parse_args()
 data=json.loads(args.baseline.read_text())
 for p in data['problems']:
  if 1<=p['id']<=6:
   PROOFS[p['id']]=next(c['proof'] for c in p['teamResults'] if c['id']==p['selectedCandidateId'])
 assert set(PROOFS)==set(range(1,7))
 args.output.mkdir(parents=True,exist_ok=True)
 rows=[];skipped=[]
 for problem,label,code in list(variants())+list(extra_variants())+list(focus_variants()):
  if code==PROOFS[problem]:
   skipped.append({'problem':problem,'label':label,'reason':'unchanged transformation; not a new candidate'})
   continue
  dest=args.output/f'P{problem:02d}'/(label+'.lean');dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(code)
  rows.append({'problem':problem,'label':label,'path':str(dest.relative_to(args.output)),'sha256':hashlib.sha256(code.encode()).hexdigest(),'startingSha256':hashlib.sha256(PROOFS[problem].encode()).hexdigest()})
 manifest={'baselineSha256':hashlib.sha256(args.baseline.read_bytes()).hexdigest(),'candidates':rows,'skippedUnchanged':skipped}
 (args.output/'manifest.json').write_text(json.dumps(manifest,ensure_ascii=False,indent=2)+'\n')
 print(json.dumps({'candidates':len(rows),'output':str(args.output)},ensure_ascii=False))
if __name__=='__main__':main()
