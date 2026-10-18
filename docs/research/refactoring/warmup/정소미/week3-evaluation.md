# Week 3: 선택 증명 길이 평가와 4·9번 재현

2026년 10월 18일 · 정소미 · 실행관리/평가/재현

## 이번에 한 일

[남성우의 Week 3 PR #19](https://github.com/Pseudo-Lab/LeanAgent/pull/19)은 Warm-up 15문제의 후보를 검증하고, `o200k_base` 토큰·heartbeat·버전 통과율을 합친 **로컬 모의 점수**로 증명을 선택했다. 그 PR은 4·9번의 새 담당 배정을 뜻하지 않는다. 이번 실험은 선택된 15개 증명의 길이를 [Week 2의 증명 길이 계산기](evidence/proof_tokens.py)로 독립적으로 다시 세고, 4·9번은 [내 기존 최종 후보](report.md)와 **같은 Lean 환경·검증기**에서 다시 실행해 비교했다.

결론부터 말하면, 선택된 15개 중 공식 Warm-up 기준 길이보다 짧은 것은 9개, 긴 것은 4개(3·4·7·9번), 같은 것은 2개다. 7·9번은 PR #19의 로컬 토큰 수가 감소했지만 Warm-up `proof_length`로는 증가했다. 4·9번의 경우 두 후보 모두 컴파일되었고, 같은 환경에서 재측정한 내 Week 2 후보가 증명 길이와 heartbeat 모두 더 낮았다. **15개 전체의 Lean 검증을 새로 한 것은 아니다.**

## 입력과 평가 기준

입력은 PR #19의 [고정 커밋 `74d2aa1`](https://github.com/Pseudo-Lab/LeanAgent/commit/74d2aa111e3594052489a70f1580cf8bed4b25cb)에 있는 `reference/benchmark_data_warmup.jsonl`, `selected.json`, `results.json` 세 파일이다. [재계산 스크립트](evidence/week3-2026-10-18/audit_selected_lengths.py)는 이 커밋에서 파일을 받아 SHA-256을 검사한다. 원본 15개의 길이가 공개 `proof_length`와 **15/15 일치**할 때만 선택 증명을 계산한다. [15문제 전체 결과 CSV](evidence/week3-2026-10-18/selected_lengths.csv)는 재계산 결과를 보존한다.

여기서 `proof_length`는 주석을 제거하고 Lean 기호를 분리해 세는 Warm-up 증명 길이 규칙을 재현한 값이다. PR #19의 `o200k_base`는 proof body 전체를 언어모델 토큰으로 세므로 단위가 다르다. 서로 다른 단위의 숫자를 직접 점수에 섞지 않았다. 표의 로컬 원후보 토큰 변화는 PR #19의 `candidate_tokens − local_baseline_tokens`이다. 원후보가 그대로 선택된 경우에만 `results.json`에서 가져왔고, 13번처럼 로컬 추출 후보가 선택된 경우에는 비워 두었다.

## 15개 선택 증명의 길이

| 문제 | PR #19 선택 | 기준 → 재계산 | 길이 변화 | PR #19 로컬 원후보 토큰 변화 |
| ---: | --- | ---: | ---: | ---: |
| 1 | P1/raw | 313 → 289 | −24 | −42 |
| 2 | P3/raw | 222 → 220 | −2 | −6 |
| 3 | P1/raw | 224 → 226 | +2 | +8 |
| **4** | P3/raw | **851 → 856** | **+5** | +9 |
| 5 | P1/raw | 1,372 → 1,370 | −2 | −3 |
| 6 | P3/raw | 1,217 → 1,217 | 0 | 0 |
| **7** | P3/raw | **408 → 412** | **+4** | **−1** |
| 8 | original | 407 → 407 | 0 | 해당 없음 |
| **9** | P2/raw | **251 → 253** | **+2** | **−2** |
| 10 | P2/raw | 1,463 → 1,459 | −4 | −8 |
| 11 | P2/raw | 1,906 → 1,844 | −62 | −105 |
| 12 | P1/raw | 1,353 → 1,350 | −3 | −4 |
| 13 | P2/extraction | 1,769 → 1,717 | −52 | 해당 없음 |
| 14 | P3/raw | 1,754 → 1,716 | −38 | −87 |
| 15 | P2/raw | 4,085 → 4,021 | −64 | −114 |

길이 증가가 곧 PR #19의 로컬 선택 오류라는 뜻은 아니다. 그 PR은 heartbeat와 버전 통과율도 점수에 반영한다. 다만 **최종 평가 지표를 Warm-up `proof_length`로 삼는다면**, 로컬 언어모델 토큰 감소만으로 증명 길이 개선을 판정할 수 없다는 것을 7·9번이 보여 준다.

## 4·9번 같은 환경 재실행

4번은 PhysLib `c48433678e8fb6306ebcd48453300c8e16058a62`, Lean `v4.32.0`에서, 9번은 CSLib `197a7be621263b84c67ca4f803f69205b36d06df`, Lean `v4.32.0`에서 실행했다. 각 문제의 참조 증명, PR #19의 선택 증명([4번](evidence/week3-2026-10-18/P4-pr19.lean), [9번](evidence/week3-2026-10-18/P9-pr19.lean)), 내 Week 2 최종 증명([4번](evidence/P4/final.lean), [9번](evidence/P9/final.lean))을 같은 [`verify_candidate.py`](evidence/verify_candidate.py)로 검사했다. 모두 원래 명제를 유지했고, 전체 파일 컴파일과 공리 검사에서 통과했으며, `sorryAx`가 없었다. 세 증명의 공리 목록은 문제별로 같았다. 아래 heartbeat는 세 후보를 같은 `#count_heartbeats` 방식으로 **이번에 다시 측정한 값**이다.

| 문제·환경 | 참조 증명 | PR #19 선택 | 정소미 Week 2 최종 |
| --- | ---: | ---: | ---: |
| 4번 · proof length | 851 | 856 | **123** |
| 4번 · heartbeat | 11,947 | 11,765 | **1,411** |
| 9번 · proof length | 251 | 253 | **79** |
| 9번 · heartbeat | 3,856 | 2,689 | **516** |

6개 실행의 [결과 JSON과 Lean 로그](evidence/week3-2026-10-18/runs/)를 보존했다. 9번의 `v4.33.0-rc2`와 `v4.31.0` 호환성은 [Week 2 기록](report.md)에 있지만, 이번 비교에서는 두 후보를 동일하게 실행할 수 있는 `v4.32.0`만 새로 측정했다. PR #19의 세 환경 전체를 내 후보까지 동일한 방법으로 다시 비교한 결과로 일반화하지 않는다.

## 다시 실행하는 방법

저장소 루트에서 아래 명령을 실행하면 고정 입력을 다운로드하고 해시·기준 길이를 검사한 뒤 15개 선택 증명의 CSV를 다시 만든다. Python 표준 라이브러리만 필요하다.

```sh
python3 docs/research/refactoring/warmup/정소미/evidence/week3-2026-10-18/audit_selected_lengths.py > /tmp/selected_lengths.csv
```

4·9번 Lean 재실행에는 위에 적은 커밋의 PhysLib/CSLib checkout, 해당 저장소의 `lean-toolchain`, `lake` 의존성 캐시가 필요하다. [PhysLib](https://github.com/leanprover-community/physlib)와 [CSLib](https://github.com/leanprover/cslib)를 복제한 뒤 각각 `git checkout`으로 위 커밋을 선택하고, 각 저장소에서 `lake exe cache get`과 `lake build Physlib.Mathematics.VariationalCalculus.Basic` 또는 `lake build Cslib.Languages.CCS.BehaviouralTheory`를 실행한다. `PHYSLIB`와 `CSLIB`를 각 checkout의 절대 경로로 지정하고 아래 명령을 `evidence/` 폴더에서 실행한다. `--candidate`를 각각 `P4/reference.lean`, `P4/final.lean` 또는 `P9/reference.lean`, `P9/final.lean`으로 바꾸면 같은 문제의 나머지 두 행을 확인할 수 있다. 이때 `--tag`와 `--workdir`도 각각 `reference` 또는 `final`용으로 바꾸어 결과가 덮어써지지 않게 한다. 결과·로그는 `--workdir`에 만들어지며 checkout 자체는 수정하지 않는다.

```sh
python3 verify_candidate.py --repo "$PHYSLIB" \
  --file Physlib/Mathematics/VariationalCalculus/Basic.lean \
  --start 99 --end 224 --hb-line 87 \
  --name "fundamental_theorem_of_variational_calculus'" \
  --statement P4/statement.lean \
  --candidate week3-2026-10-18/P4-pr19.lean \
  --workdir /tmp/leanagent-week3-P4 --tag selected \
  --lean-arg=-Dwarn.sorry=false --lean-arg=-Dweak.says.verify=true

python3 verify_candidate.py --repo "$CSLIB" \
  --file Cslib/Languages/CCS/BehaviouralTheory.lean \
  --start 311 --end 372 --hb-line 310 \
  --name Cslib.CCS.bisimilarity_congr_choice \
  --statement P9/statement.lean \
  --candidate week3-2026-10-18/P9-pr19.lean \
  --workdir /tmp/leanagent-week3-P9 --tag selected \
  --extra-import Mathlib.Util.CountHeartbeats
```

## 모임에서 결정할 점

1. 후보 비교 표에 `o200k_base`와 Warm-up `proof_length`를 별도 열로 둘지, 실제 선택 기준을 어느 쪽으로 둘지 정한다.
2. 이미 검증된 4·9번 후보를 다음 전체 실험의 후보 풀에 넣고, 같은 검증기·환경으로 재선택할지 정한다.
3. 전체 15개에 대해서도 동일한 Lean 재실행을 할 범위와 비용을 정한다. 이번 PR의 15개 길이 감사는 정적 재계산이고 Lean 재실행은 4·9번에 한정된다.

공식 Arena에 후보를 제출하지 않았으므로, 새 후보의 공식 점수나 공식 worker에서의 실행 성공은 주장하지 않는다.
