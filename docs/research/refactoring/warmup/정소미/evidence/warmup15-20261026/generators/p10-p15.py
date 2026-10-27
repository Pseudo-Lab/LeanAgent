from pathlib import Path
import json,hashlib,sys
import argparse
parser=argparse.ArgumentParser(description='Generate the frozen proof-edit candidates using only the saved starting selection; validation is performed separately by Lean.')
parser.add_argument('--baseline',type=Path,required=True)
parser.add_argument('--output',type=Path,required=True)
args=parser.parse_args()
out=args.output.resolve();out.mkdir(parents=True,exist_ok=True)
snapshot=json.loads(args.baseline.read_text())
by_id={p['id']:p for p in snapshot['problems']}
entries=[]
def add(p,id,code,method):
 f=out/f'P{p:02d}'/f'{id}.lean';f.parent.mkdir(exist_ok=True);f.write_text(code)
 entries.append({'problem':p,'id':id,'path':str(f),'sha256':hashlib.sha256(code.encode()).hexdigest(),'method':method,'status':'not_yet_run','paperReferences':({10:['2607.09564'],11:['2607.09564','2507.20267'],12:['2610.22339','2507.20267'],13:['2610.22339'],14:['2610.22339'],15:['2610.22339']}[p]),'parentCandidateHash':by_id[p]['candidateHash']})
for p in range(10,16):
 row=by_id[p];s=next(c['proof'] for c in row['teamResults'] if c['id']==row['selectedCandidateId']);assert hashlib.sha256(s.encode()).hexdigest()==row['candidateHash'];(out/f'P{p:02d}').mkdir(exist_ok=True);(out/f'P{p:02d}/starting.lean').write_text(s)
 if p==10:
  add(p,'card-trans-eq',s.replace('exact Finset.card_image_le.trans (by simp)','exact Finset.card_image_le.trans_eq (Finset.card_univ.trans (Fintype.card_fin _))'),'기대 타입이 주어진 직접 등식 연결; 준비된487토큰 수리안의 실제 검증')
  add(p,'card-trans-eq-simp',s.replace('exact Finset.card_image_le.trans (by simp)','exact Finset.card_image_le.trans_eq (by simp)'),'기수 상한의 마지막 등식 목표를 기대 타입과 함께 검사')
  add(p,'card-restricted-simp',s.replace('exact Finset.card_image_le.trans (by simp)','exact Finset.card_image_le.trans (by simp only [Finset.card_univ, Fintype.card_fin, le_refl])'),'기수 목표의 전역 simp를 명시된 정리만으로 제한')
 elif p==11:
  a=s.index('      have h : j.val * 2');b=s.index('    ⟩) +',a)
  cut=s[:a]+'''      simpa only [Nat.add_zero] using
        mul_two_add_bit_lt_two_pow (c := ℓ - i) (a := j) (b := ℓ - (↑i + 1))
          (i := 0) (by omega) (by omega)
'''+s[b:]
  add(p,'index-lemma',cut,'타입에 맞는 기존 인덱스 경계 정리 재사용으로 중복 산술 증명 삭제')
  a=cut.index('  have h_eval_qMap_x₀');b=cut.index('  have h_fiber_diff',a)
  joined=cut[:a]+'''  have h_eval_qMap (j : Fin 2) :
      (AdditiveNTT.qMap 𝔽q β ⟨i, by omega⟩).eval (fiberMap j).val = y := by
    have h := iteratedQuotientMap_k_eq_1_is_qMap 𝔽q β h_ℓ_add_R_rate i (by omega) (fiberMap j)
    simp only [Subtype.eq_iff] at h
    rw [h.symm]
    exact is_fiber_iff_generates_quotient_point 𝔽q β i (steps := 1) (by omega)
      (x := fiberMap j) (y := y).mpr (by rw [pointToIterateQuotientIndex_qMap_total_fiber_eq_self])
'''+cut[b:]
  joined=joined.replace('h_eval_qMap_x₀','h_eval_qMap 0').replace('h_eval_qMap_x₁','h_eval_qMap 1')
  add(p,'shared-fiber-evaluation',joined,'같은 qMap 평가 증명을 Fin2 인자로 일반화하여 한 번 재사용')
  add(p,'index-lemma-ring1',cut.replace(':= by ring\n',':= by ring1\n').replace('rw [h_fiber_diff]; ring','rw [h_fiber_diff]; ring1'),'기존 정리 재사용 후 두 다항식 계산을 ring1로 제한')
 elif p==12:
  a=s.index('          have h_snoc :');b=s.index('          let P :',a)
  oldproof=s[a:b]
  brief=oldproof[:oldproof.index(':= fun r => by')]+':= fun r => Fin.snoc_init_self r\n'
  add(p,'snoc-library',s[:a]+brief+s[b:],'수동 Fin 마지막 원소 분해를 기존 Fin.snoc_init_self 정리로 대체')
  direct=(s[:a]+s[b:]).replace('simp_rw [h_snoc] at h_split','simp_rw [Fin.snoc_init_self] at h_split')
  add(p,'snoc-direct',direct,'지역 snoc 재조립 보조정리 자체를 제거하고 기존 정리를 직접 재작성')
  a=direct.index('            funext i\n');b=direct.index('          rw [hu.symm]',a)
  add(p,'snoc-direct-fin-cases',direct[:a]+'            ext i\n            fin_cases i <;> rfl\n'+direct[b:],'snoc 정리 재사용과 Fin2 함수 외연성 증명 직접 분기')
 elif p==13:
  add(p,'simp-all-arithmetic',s.replace('simp (disch := omega) only [Nat.add_sub_assoc, ih]','simp only [Nat.add_sub_assoc (by omega), ih _ (by omega)]'),'귀납 호출의 조건을 명시하여 지역 산술 탐색을 제한')
  add(p,'final-simpa',s.replace('  convert (hp (n-a)).symm using 2 <;> omega','  simpa only [Nat.add_sub_of_le hn, Nat.sub_add_cancel hab.le, Nat.add_sub_assoc hn] using (hp (n-a)).symm'),'최종 periodic 인덱스 정규화를 명시된 자연수 항등식으로 대체')
 elif p==14:
  add(p,'pow-pred',s.replace('  rw [show Fintype.card S = (Fintype.card S - 1) + 1 by omega, pow_succ] at hcard','  rw [← Nat.sub_add_cancel hn, pow_succ] at hcard'),'기수 양성으로 Nat.sub_add_cancel을 직접 적용하여 산술 탐색 삭제')
  add(p,'maximal-direct',s.replace('    apply Finset.Subset.antisymm hPQ\n    intro T hT\n    by_contra hT\'','    apply Finset.Subset.antisymm hPQ\n    intro T hT\n    by_contra hT\'').replace('  have hcard := hP.is_max_iff_card_eq.mp (by','  have hcard := hP.is_max_iff_card_eq.mp (by').replace('  rw [Fintype.card_set] at hcard\n  have hn := Fintype.card_pos (α := S)\n  rw [show Fintype.card S = (Fintype.card S - 1) + 1 by omega, pow_succ] at hcard\n  omega','  have hn := Fintype.card_pos (α := S)\n  rw [Fintype.card_set, show Fintype.card S = (Fintype.card S - 1) + 1 by omega, pow_succ] at hcard\n  omega'),'같은 정리 적용의 연속 rewrite 결합으로 중간 tactic 명령 제거')
 elif p==15:
  add(p,'key-simp-ring',s.replace('[(subst h; ring); simp]','[ (subst h; ring1); simp ]'),'자리 교체 합 항등식의 대수 계산을 ring1로 제한')
  add(p,'final-ring1',s.replace(' using 1\n    ring',' using 1\n    ring1'),'최종 나눗셈 증거의 다항식 정규화를 ring1로 제한')
  add(p,'key-sum-congr',s.replace('exact Finset.sum_congr rfl fun j _ => by split_ifs with h <;> [(subst h; ring); simp]','apply Finset.sum_congr rfl\n    intro j _\n    split_ifs with h\n    · subst h; ring1\n    · simp'),'합 보존 증명에서 기대 타입을 먼저 고정한 지역 계산')
# Diagnostic repair after the initial snoc-direct compiler failure.
add(12,'snoc-init-fold',(out/'P12/snoc-direct.lean').read_text().replace('simp_rw [Fin.snoc_init_self] at h_split','simp_rw [← Fin.init_def, Fin.snoc_init_self] at h_split'),'실제 simp no-progress 오류를 받아 Fin.init 표기를 먼저 접은 뒤 snoc_init_self 적용')
# Repairs from the actual primary-run compiler diagnostics.
for name in ['index-lemma', 'shared-fiber-evaluation']:
 code=(out/'P11'/f'{name}.lean').read_text().replace('simpa only [Nat.add_zero] using', 'simpa only [Fin.val_zero, Nat.add_zero] using')
 if name=='shared-fiber-evaluation':
  code=code.replace('simp only [h_P_i_eval, Fin.eta,', 'simp only [x₀, x₁, h_P_i_eval, Fin.eta,')
 add(11,name+'-repair',code,'실제 타입 오류 수리: Fin 0의 자연수 coercion을 정규화하고 공유 fiber 표현을 펼쳐 원래 목표와 정렬')
(out/'candidate-manifest.json').write_text(json.dumps({'schemaVersion':1,'startingSnapshot':str(args.baseline),'startingSnapshotSha256':hashlib.sha256(args.baseline.read_bytes()).hexdigest(),'candidates':entries},ensure_ascii=False,indent=2)+'\n')
for e in entries:print(e['problem'],e['id'],e['sha256'][:10])
