# Week 3: 선택 증명 길이 평가와 4·9번 재현

2026년 10월 18일 · 정소미 · 실행관리/평가/재현

## 이번에 한 일

[남성우의 Week 3 PR #19](https://github.com/Pseudo-Lab/LeanAgent/pull/19)은 Warm-up 15문제의 후보를 검증하고, `o200k_base` 토큰·heartbeat·버전 통과율을 합친 **로컬 모의 점수**로 증명을 선택했다. 그 PR은 4·9번의 새 담당 배정을 뜻하지 않는다. 이번 실험은 선택된 15개와 선택 전 원후보 45개의 길이를 [Week 2의 증명 길이 계산기](evidence/proof_tokens.py)로 다시 세고, 4·9번은 [내 기존 최종 후보](report.md)와 **같은 Lean 환경·검증기**에서 다시 실행해 비교했다. 4·9번의 반복 실행과 9번의 세 Lean 버전 비교도 추가했다.

선택된 15개 중 Warm-up 기준 길이보다 짧은 것은 9개, 긴 것은 4개(3·4·7·9번), 같은 것은 2개다. 선택 전 원후보 중 **PR #19 결과상 유효한** 35개에서는 두 토큰 지표의 증감 방향이 반대인 사례가 5개였다. 4·9번의 경우 비교한 증명 모두 컴파일되었고, 같은 환경에서 재측정한 내 Week 2 후보가 증명 길이와 heartbeat 모두 더 낮았다. 9번의 두 후보는 세 지정 버전에서 모두 통과했다. **15개 전체의 Lean 검증을 새로 한 것은 아니다.**

## 논문에서 가져온 평가 원칙

| 참고 논문 | 확인한 원칙 | 이번 실험에 적용한 부분 |
| --- | --- | --- |
| [Lean Refactor](https://www.alphaxiv.org/pdf/2605.20244) | 증명 길이, 컴파일 비용, 버전 호환성을 별도 축으로 평가한다. 연구 저장소의 비용에는 선언 단위 heartbeat를 쓴다. | 토큰 지표의 방향 차이를 확인하고, 4·9번 heartbeat와 9번 세 버전 통과 여부를 분리해 기록했다. |
| [LeanDojo](https://www.alphaxiv.org/pdf/2306.15626) | 공개 코드·데이터와 고정 Mathlib 커밋을 제공하고, 증명을 실제 Lean 환경에서 상호작용하며 평가한다. | PR 입력 SHA-256과 프로젝트 커밋을 고정하고, 4·9번은 전체 원본 파일 문맥에서 Lean으로 다시 검사했다. |
| [Arvan 등, EMNLP 2022](https://aclanthology.org/2022.emnlp-main.150.pdf#page=2) | 코드 공개만으로는 재현이 충분하지 않으며 작은 실행 예제와 결과 생성 스크립트가 도움이 된다. | 입력 해시, 재계산 스크립트, 원후보·선택 결과 CSV, Lean 실행 로그를 함께 남겼다. |

이 논문들의 성능 수치를 재현한 것은 아니다. 논문에서 제시한 **평가·기록 방법**을 이번 Warm-up 자료에 적용했다. Lean 프로젝트의 의존성 캐시는 별도로 준비해야 하므로 이 PR 자체가 완전한 독립 실행 패키지는 아니다.

## 입력과 평가 기준

입력은 PR #19의 [고정 커밋 `74d2aa1`](https://github.com/Pseudo-Lab/LeanAgent/commit/74d2aa111e3594052489a70f1580cf8bed4b25cb)에 있는 `reference/benchmark_data_warmup.jsonl`, `selected.json`, `results.json`, `candidates.jsonl`이다. [선택 증명 재계산](evidence/week3-2026-10-18/audit_selected_lengths.py)과 [원후보 감사](evidence/week3-2026-10-18/audit_raw_candidates.py)는 이 커밋의 파일을 받아 SHA-256을 검사한다. 원본 15개의 길이가 공개 `proof_length`와 **15/15 일치**하고 원후보 45개의 저장된 원본 body도 각 기준 길이와 **45/45 일치**하는 것을 확인했다. [선택 결과](evidence/week3-2026-10-18/selected_lengths.csv)와 [원후보 결과](evidence/week3-2026-10-18/raw_candidate_metrics.csv)를 CSV로 보존한다.

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

## 선택 전 45개 원후보 감사

PR #19의 고정 `candidates.jsonl`에는 15문제 × P1·P2·P3의 원후보 45개가 있다. PR #19의 `raw_outcome`에 따라 7개는 invalid, 8번의 3개 슬롯은 제외 대조군이며, 나머지 **35개는 PR #19에서 유효하다고 기록한 원후보**로 분류했다. 이 35개의 Warm-up 길이는 기준보다 **18개 짧고, 8개 길고, 9개 같았다**. 35개를 내가 Lean으로 다시 검사한 결과가 아니며, invalid 후보가 짧아 보여도 개선 성공으로 세지 않았다.

두 토큰 지표의 **증감 방향이 정반대**인 검증 후보는 5개다. 2/P1, 3/P2, 7/P3, 9/P2는 `o200k_base` 토큰이 줄었지만 Warm-up 길이는 늘었고, 13/P3은 반대였다. 단위가 달라 숫자의 크기를 직접 비교하지 않고, 증가·감소의 방향만 비교했다. [45개 전체 표](evidence/week3-2026-10-18/raw_candidate_metrics.csv)에 invalid와 제외 대조군도 그대로 표시했다.

선택 규칙의 민감도를 보기 위해 PR #19의 **원후보 점수**에서 길이 항만 `o200k_base` 감소율에서 Warm-up 길이 감소율로 바꾸고 heartbeat·버전 항은 그대로 두었다. 이는 새 실험용 가상 점수이며 공식 Arena 점수가 아니다. 공개된 원후보 점수를 토큰·heartbeat 필드와 재구성할 수 있는 13문제에서 원본 fallback까지 포함해 비교했더니, [7번은 P3→P1, 10번은 P2→P1](evidence/week3-2026-10-18/score_sensitivity.csv)로 최선 원후보가 바뀌었다. 8번은 제외 대조군이고, 13번은 공개 요약 필드만으로 원점수를 재구성하지 못해 이 민감도 계산에서 제외했다. 13번의 **길이 감사 자체는 포함**된다.

## 4·9번 같은 환경 재실행

4번은 PhysLib `c48433678e8fb6306ebcd48453300c8e16058a62`, Lean `v4.32.0`에서, 9번은 CSLib `197a7be621263b84c67ca4f803f69205b36d06df`, Lean `v4.32.0`에서 실행했다. 각 문제의 참조 증명, PR #19의 선택 증명([4번](evidence/week3-2026-10-18/P4-pr19.lean), [9번](evidence/week3-2026-10-18/P9-pr19.lean)), 내 Week 2 최종 증명([4번](evidence/P4/final.lean), [9번](evidence/P9/final.lean))을 같은 [`verify_candidate.py`](evidence/verify_candidate.py)로 검사했다. 모두 원래 명제를 유지했고, 전체 파일 컴파일과 공리 검사에서 통과했으며, `sorryAx`가 없었다. 세 증명의 공리 목록은 문제별로 같았다. 아래 heartbeat는 세 후보를 같은 `#count_heartbeats` 방식으로 **이번에 다시 측정한 값**이다.

| 문제·환경 | 참조 증명 | PR #19 선택 | 정소미 Week 2 최종 |
| --- | ---: | ---: | ---: |
| 4번 · proof length | 851 | 856 | **123** |
| 4번 · heartbeat | 11,947 | 11,765 | **1,411** |
| 9번 · proof length | 251 | 253 | **79** |
| 9번 · heartbeat | 3,856 | 2,689 | **516** |

6개 실행의 [결과 JSON과 Lean 로그](evidence/week3-2026-10-18/runs/)를 보존했다. 여기서 heartbeat는 PR #19의 IO 차이 계측값을 가져온 것이 아니라 두 후보를 같은 `#count_heartbeats` 검증기로 다시 잰 값이다.

### 반복성과 버전 호환성

동일한 `v4.32.0` checkout에서 4·9번의 PR #19 후보와 내 후보를 **각각 세 번** 실행했다. 네 후보 모두 3/3회 컴파일·공리 검사를 통과했고, 증명 길이와 heartbeat가 세 번 내내 같았다([12회 결과 표](evidence/week3-2026-10-18/repeatability.csv), [반복 실행 원본](evidence/week3-2026-10-18/runs/repeats/)). 벽시계 실행 시간은 실행마다 달랐고, import·캐시·호스트 부하를 분리하지 않았으므로 이번 비교 지표로 쓰지 않았다.

9번은 두 후보와 참조 증명을 지정된 CSLib 세 커밋에서 다시 실행했다. 같은 body를 버전마다 수정하지 않았고, 세 증명 모두 **3/3 버전에서 컴파일·공리 검사 통과**했다. 아래의 길이/heartbeat는 매 버전의 같은 검증기로 잰 값이다([전체 CSV](evidence/week3-2026-10-18/cross_version_p9.csv), [추가 버전 원본 로그](evidence/week3-2026-10-18/runs/cross-version/)).

| 9번 Lean · CSLib 커밋 | 참조 증명 | PR #19 선택 | 정소미 Week 2 최종 |
| --- | ---: | ---: | ---: |
| `v4.31.0` · `8ea71c8` | 251 / 3,859 | 253 / 2,690 | **79 / 516** |
| `v4.32.0` · `197a7be` | 251 / 3,856 | 253 / 2,689 | **79 / 516** |
| `v4.33.0-rc2` · `3aa9d44` | 251 / 3,858 | 253 / 2,690 | **79 / 510** |

4번은 지정 버전이 하나라 같은 방식의 버전 간 비교 대상이 아니다. 9번 결과도 이 세 고정 커밋에서의 로컬 실행 범위에 한정된다.

## 다시 실행하는 방법

저장소 루트에서 아래 명령을 실행하면 고정 입력을 다운로드하고 해시·기준 길이를 검사한 뒤 선택된 15개와 원후보 45개의 결과 파일을 다시 만든다. Python 표준 라이브러리만 필요하다.

```sh
python3 docs/research/refactoring/warmup/정소미/evidence/week3-2026-10-18/audit_selected_lengths.py > /tmp/selected_lengths.csv
python3 docs/research/refactoring/warmup/정소미/evidence/week3-2026-10-18/audit_raw_candidates.py --output-dir /tmp/leanagent-raw-audit
```

4·9번 Lean 재실행에는 위에 적은 커밋의 PhysLib/CSLib checkout, 해당 저장소의 `lean-toolchain`, `lake` 의존성 캐시가 필요하다. [PhysLib](https://github.com/leanprover-community/physlib)와 [CSLib](https://github.com/leanprover/cslib)를 복제한 뒤 각각 `git checkout`으로 위 커밋을 선택하고, 각 저장소에서 `lake exe cache get`과 `lake build Physlib.Mathematics.VariationalCalculus.Basic` 또는 `lake build Cslib.Languages.CCS.BehaviouralTheory`를 실행한다. `PHYSLIB`와 `CSLIB`를 각 checkout의 절대 경로로 지정하고 아래 명령을 `evidence/` 폴더에서 실행한다. `--candidate`를 각각 `P4/reference.lean`, `P4/final.lean` 또는 `P9/reference.lean`, `P9/final.lean`으로 바꾸면 같은 문제의 나머지 두 행을 확인할 수 있다. 이때 `--tag`와 `--workdir`도 후보별·반복별로 다르게 지정해 결과가 덮어써지지 않게 한다. 9번의 버전 비교에는 `CSLIB`를 위 표의 세 커밋 checkout으로 바꾸되 후보 body는 그대로 둔다. 결과·로그는 `--workdir`에 만들어지며 checkout 자체는 수정하지 않는다.

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

1. 후보 비교 표에 `o200k_base`와 Warm-up `proof_length`를 별도 열로 두고, 실제 선택 점수에 어느 길이 지표를 넣을지 정한다. 원후보 7·10번의 가상 재선택 결과는 이 결정에 민감하다.
2. 이미 검증된 4·9번 후보를 다음 전체 실험의 후보 풀에 넣고, 같은 검증기·환경으로 재선택할지 정한다.
3. 전체 15개에 대해서도 동일한 Lean 재실행을 할 범위와 비용을 정한다. 이번 PR의 15·45개 길이 감사는 정적 재계산이고 Lean 재실행은 4·9번에 한정된다.

공식 Arena에 후보를 제출하지 않았으므로, 새 후보의 공식 점수나 공식 worker에서의 실행 성공은 주장하지 않는다.
