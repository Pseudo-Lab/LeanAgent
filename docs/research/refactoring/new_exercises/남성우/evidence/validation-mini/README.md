# Lean Refactor Arena 검증·수리 Harness 소규모 검증 데이터 (`validation-mini`)

이 디렉토리는 [`gemini-validation-data-request.md`](../../../../../agent_repair/남성우/evidence/gemini-validation-data-request.md) 및 [`escalation-policy-and-data-recipe.md`](../../../../../agent_repair/남성우/evidence/escalation-policy-and-data-recipe.md)(2026-10-15 보완 계약 반영)에 따라 생성·실행된 소규모 smoke/regression 데이터셋입니다.

- **실제 Lean 실행 사례 8건(`R01`~`R08`) + 추가 변형 1건(`R06b`)**: 모두 실제 `lake env lean --json`으로 검증 및 로컬 수리 목록을 실행했습니다.
  - **Arena warm-up 파생 5건 (`source_kind="arena_derived"`)**: `R02`, `R03`, `R06`, `R06b`, `R07`, `R08` (warm-up 문제 1, 2, 3에서 파생).
  - **교육용 소규모 정리 3건 (`source_kind="toy"`)**: `R01`, `R04`, `R05` (Mathlib/Aesop 환경에서 작성).
- **합성 정책 fixture 4묶음 (`P01`~`P04`)**: 총 43개 정책 입력(`synthetic=true`)과 12개 selector 계약 테스트 케이스(`selector_contract_cases.json`).
- **외부 LLM API 호출 없음**: 모든 프롬프트는 [`escalation_policy.py`](../escalation_policy.py)의 오프라인 렌더러 출력입니다.

---

## 1. 고정 환경 및 출처 (`environment.json`, `manifest.json`)

| 환경 키 | 프로젝트 경로 | Lean 버전 / Toolchain | Repo Commit | `lake-manifest.json` SHA-256 | Uncommitted 상태 및 처리 |
|---|---|---|---|---|---|
| `strata` | `/Users/sungwoo/lean_project/refactor_arena/strata` | Lean 4.26.0 (`leanprover/lean4:v4.26.0`, commit `d8204c9fd894`) | `451e5f047bafa010d178856db76c00029bfa4d7f` | `5aab41f14cc5...b244c` (`plausible` `b949552f`) | `M Strata/Transform/CallElimCorrect.lean` (diff SHA-256 `f0247de9...`). 워킹 트리를 덮어쓰지 않고 `git show HEAD:...` 원본을 `sources/`에 복사해 재현. |
| `mathlib_toy` | `/Users/sungwoo/lean_project/autoformalization_lab` | Lean 4.35.0-rc4 (`leanprover/lean4:v4.35.0-rc4`, commit `c29b6dda4f7c`) | `454cc4cd2f28c71eaa3f37df40ef5616a96b947e` | `c81d46e83558...` (`mathlib` `e6bbacd0`, `aesop` `04879b1e`) | 기존 파일 수정 없이 `validation-mini/sources/toy/*.lean` 독립 파일을 `lake env lean`으로 실행. |

- **Arena seed 출처**: `/Users/sungwoo/lean_project/refactor_arena/benchmark_data_warmup.jsonl` (전체 SHA-256: `6209680cf00cde0765b77b24834cd72c64dd585b2f7e3f2a58209980ab59a804`). 1~3번 레코드를 `sources/warmup_seeds_1_3.jsonl`에 사본 보관했습니다.
  - **줄 번호 주의**: `benchmark_data_warmup.jsonl`의 `start_line` 값(`2964`, `2733`, `950`)은 `git HEAD` 원본의 실제 줄 번호(`3089`, `2858`, `931`)와 다릅니다. 모든 선언 위치는 추측하지 않고 파일 내 유일한 `src` 문자열 정합으로 고정했습니다.
- **Tactic 가용성**: `strata` 환경에는 `Mathlib`과 `Aesop`이 없으므로 기본 import를 임의 확장하지 않았습니다(`aesop?` 로컬 수리는 `strata` 케이스에서 `skipped`로 기록). `aesop?` 추출 사례(`R04`)는 `Aesop`이 설치된 `mathlib_toy` 환경에서 실행했습니다.

---

## 2. 고정 로컬 수리 목록 (`local-ops-v1`)

케이스 실행 전에 [`reproduce.py`](reproduce.py)의 `LOCAL_POLICY_V1`로 고정했으며, 케이스별 기대 결과를 맞추기 위해 사후 수정하지 않았습니다.

1. `delete_span` (`unsolved goals` 오류인 경우 목표를 닫을 수 없으므로 `skipped`)
2. `replace_span` with `assumption`
3. `replace_span` with `rfl`
4. `replace_span` with `omega`
5. `replace_span` with `simp_all`
6. `replace_span_extract` with `simp?` (`Try this:` 제안이 출력되면 치환 후 전체 파일 재검증)
7. `replace_span_extract` with `exact?` (`Try this:` 제안이 출력되면 치환 후 전체 파일 재검증)
8. `replace_span_extract` with `aesop?` (환경에 `Aesop`이 없으면 `skipped`; `Try this: sorry`는 거부)

- **적용 위치 규칙**: 대상 선언 내부의 첫 번째 오류 줄(`first_error`)과 그보다 들여쓰기가 깊은 후속 줄을 텍스트 휴리스틱 span으로 잡습니다. 첫 오류가 `unsolved goals`이면 블록을 치환하는 대신 블록 끝에 tactic을 추가합니다.
- **전체 재검증 규칙**: 국소 오류가 사라져도(`local_error_cleared=true`) 뒤쪽을 포함한 전체 파일 컴파일과 `#print axioms` 검사가 통과(`full_replay_valid`)해야만 로컬 성공으로 인정합니다.

---

## 3. 재현 명령

```bash
cd docs/research/refactoring/new_exercises/남성우/evidence/validation-mini

# 1) Lean 없이 저장된 request.json으로부터 decision.json 재렌더링
python3 reproduce.py policy

# 2) Lean 없이 합성 정책 fixture (P01..P04, 43개 입력 + 12개 selector 케이스) 검증
python3 reproduce.py fixtures

# 3) 실제 Lean 재실행 (단일 케이스 또는 전체)
python3 reproduce.py case R01
python3 reproduce.py all

# 4) manifest.json 갱신
python3 reproduce.py manifest
```

---

## 4. 실제 Lean 사례 요약 (`R01`~`R08` 및 `R06b`)

| ID | 출처 (`source_kind`) | 변형 원인 (`expected_intent`) | 실제 Lean 결과 (`observed_result`) | 실패 직전 상태 (`pre_error_state`) | 고정 로컬 수리 결과 (`local-ops-v1`) | 정책 결정 (`decision.json` / `.configured_budget.json`) | 측정값 (비공백 문자 수 / 로컬 HB 추정) | 데이터 한계 및 비고 |
|---|---|---|---|---|---|---|---|---|
| **R01** | `toy` (`r01_and_swap`) | `constructor` 두 분기를 `exact ⟨h.1.1, h.2⟩`로 합치며 projection 순서를 반대로 둠 | `invalid`: `Application type mismatch` (`h.left.left : P`, expected `R`) | `trace_state`로 `⊢ R ∧ P` 캡처 (`trusted=false`) | **성공 (`local_success`)**: op #1(`delete_span`)은 해당 줄 오류만 지우고 `unsolved goals` 발생, op #5(`simp_all`)가 전체 재검증 통과 | `MEASURE` (유효 후보 도달, 공식 token 미측정) | 원본 `33`자 / `13` HB, 로컬수리 `10`자 / `14` HB, gold `18`자 / `12` HB | 프롬프트 없음(로컬 해결 정상). 단일 환경만 실행. |
| **R02** | `arena_derived` (`warmup-2: extractedOldExprInVars`) | 이미 선언 변수인 `post`를 도입부에서 `intro post Hnorm`으로 다시 도입 | `invalid`: `post`가 `NormalizedOldExpr post`를 받고 `Hnorm`이 결론의 원소를 받아 줄 2872 `No goals to be solved` 및 후속 `case` 태그 불일치 등 6개 오류 | 줄 2872에서 빈 목표 캡처 (`trusted=false`; 첫 진단 위치가 실제 원인 줄 2863보다 뒤쪽) | **실패 (`exhausted`)**: 1~7번 모두 실패 (`simp?`/`exact?` 제안 없음), 8번 `aesop?`은 환경 미지원 `skipped` | `PRICE_REQUEST` / 설정 예산 시 `EMIT_LLM_PROMPT` (`mode=repair`, `scope=body`) | 원본 `1174`자 / `2697` HB, gold `1173`자 / `2697` HB | 첫 오류 위치가 원인(`intro post Hnorm`)이 아닌 후속 분기여서 로컬 치환이 원인을 건드리지 못함. |
| **R03** | `arena_derived` (`warmup-2: extractedOldExprInVars`) | 넓은 `simp [...]`를 `simp only [...]`로 바꾸며 `Lambda.LExpr.LExpr.getVars` 규칙을 누락 | `invalid`: 뒤쪽 `<;> try simp_all` 덕분에 초반은 지나가나 `case app` 내부 줄 2885 등 9곳에서 `unsolved goals` 발생 | 줄 2885 직전 goal 캡처 (`trusted=false`) | **실패 (`exhausted`)**: op #2~#5가 첫 `unsolved goals` 지점은 닫았으나(`original_error_cleared_full_replay_failed`) 나머지 8개 지점이 남아 전체 재검증 실패 | `PRICE_REQUEST` / 설정 예산 시 `EMIT_LLM_PROMPT` (`mode=repair`, `scope=body`) | 원본 `1174`자 / `2697` HB, gold `1178`자 / `2509` HB | Gold는 `simp only`에 누락 규칙을 복원하여 의도 보존 + HB 감소(2697→2509). |
| **R04** | `toy` (`r04_inter_union`) | 명시적 `obtain`/`rcases` 증명을 단일 `aesop` 호출로 치환 | **`valid`**: 후보 자체가 통과 | `null` (후보 valid) | Valid 경로 추출: `aesop?`가 `simp_all only [Set.mem_inter_iff, Set.mem_union, true_and]`를 제안했고 치환 본문도 `valid` | `MEASURE` (공식 token 미측정으로 성급한 최적화 호출 차단) | 원본 `76`자 / `68` HB, raw `aesop` `7`자 / **`119` HB**, 추출 script `56`자 / **`69` HB** | Raw `aesop`은 글자 수는 짧지만 HB가 68→119로 증가; 추출 script는 HB를 69로 회복. |
| **R05** | `toy` (`r05_mem_cons`) | `x ∈ a :: l`을 `simp only [List.mem_cons]`로 바꾼 뒤 `right` 대신 `left`를 성급히 선택 | `invalid`: `exact h`에서 `Type mismatch` (`h : x ∈ l`, expected `x = a`) | `trace_state`로 막다른 목표 `⊢ x = a` 캡처 (`trusted=false`) | **실패 (`exhausted`)**: 모든 로컬 수리가 `exact h` 줄만 건드리므로 `x = a`를 증명할 수 없어 실패 (`aesop?`는 `Try this: sorry`를 출력하여 거부됨) | `PRICE_REQUEST` / 설정 예산 시 `EMIT_LLM_PROMPT` (`mode=repair`, `scope=body`) | 원본 `36`자 / `28` HB, gold(`exact Or.inr h`) `37`자 / `29` HB | 앞선 `left` 선택이 문제이므로 실패 줄만 고치는 로컬 수리로는 복구 불가. |
| **R06** | `arena_derived` (`warmup-3: InitsUpdatesComm`) | `induction Hup generalizing σ''`에서 `generalizing σ''`를 삭제 | **`valid` (예상 밖 통과)**: `UpdateStates` 귀납에서 `σ''`가 재귀 호출마다 바뀌지 않아 `generalizing` 없이도 통과 | `null` (후보 valid) | Valid 경로 추출: 본문 내 `simp_all?`, `simp?` 3곳에서 `simp_all only [...]`, `simp only [...]` 제안 추출 및 재검증 `valid` | `MEASURE` (공식 token 및 다중 버전 미완결) | 원본 `1209`자 / `4676` HB, 후보 **`1194`자 / `2980` HB**, 추출0 `1224`자 / `2970` HB | 실패할 것으로 예측했으나 실제 Lean에서 통과하고 HB도 감소(4676→2980)함. 정직하게 `valid`로 기록하고 아래 `R06b`를 추가 제작. 지정 3개 버전 중 `v4.26.0` 1개만 검증됨(`robustness_incomplete`). |
| **R06b** | `arena_derived` (`warmup-3: InitsUpdatesComm`) | 귀납 직전 보조단계 `have Hk : (isDefined σ' ks) := UpdateStatesDefined Hup`를 삭제하여 귀납 문맥 손실 | `invalid`: 귀납 가설 `ih`의 전제 `isDefined σ₀ xs`를 닫던 마지막 줄 981 `simp_all`에서 `simp_all made no progress` 오류 | 줄 981 직전 `⊢ False` 상태 캡처 (`trusted=false`) | **실패 (`exhausted`)**: 1~7번 모두 실패 (보조 가설 `Hk`가 귀납 이전에 빠져 있어 마지막 줄 로컬 수리로 해결 불가) | `PRICE_REQUEST` / 설정 예산 시 `EMIT_LLM_PROMPT` (`mode=repair`, `scope=body`) | 원본/gold `1209`자 / `4676` HB | `R06`이 valid로 관찰되어 추가한 실제 귀납 문맥 손실 → escalation 사례. |
| **R07** | `arena_derived` (`warmup-1: substOldPostSubset`) | 프로젝트 로컬 보조정리 `List.Subset.app` 8곳을 존재하지 않는 표준 라이브러리풍 이름 `List.append_subset_of_subset`으로 일괄 변경 | `invalid`: 8곳에서 `Unknown constant List.append_subset_of_subset` | 첫 발생 줄 3124 직전 goal 캡처 (`trusted=false`) | **실패 (`exhausted`)**: 첫 발생 지점에 op #1(`delete_span`) 적용 시 해당 줄 오류는 사라지나 하위 목표 미해결 및 나머지 7곳의 unknown constant로 전체 재검증 실패 | `PRICE_REQUEST` / 설정 예산 시 `EMIT_LLM_PROMPT` (`mode=repair`, `scope=body`) | 원본 `1670`자 / `5176` HB, gold `1745`자 / `5248` HB | Gold 1차 시도(`refine List.append_subset.mpr ⟨?_, ?_⟩`)가 코어 라이브러리 정리만으로 전체 검증 통과하여 리팩터링 의도 보존. |
| **R08** | `arena_derived` (`warmup-1: substOldPostSubset`) | `case fvar`에서 `rename_i m name ty2`를 불필요하다고 보고 삭제 | `invalid`: `m`은 바깥 스코프 변수에 우연히 묶여 `simp at m`은 통과하고, 다음 줄 3098 `simp at name`에서 `Unknown identifier name` 발생 | 줄 3098 직전 goal 캡처 (`trusted=false`: 목표에 `m✝ name✝ ty✝`가 hygiene 이름으로 남아 있음) | **실패 (`exhausted`, 국소 성공 후 전체 실패 확인)**: op #5(`simp_all`), op #6(`simp?` → `simp only [List.mem_append, ...]`), op #7(`exact?` → `exact List.mem_append_left [h1] Hin`)이 모두 현재 목표는 닫았으나(`original_error_cleared_full_replay_failed`), 바로 뒤 `simp at ty2` / `simp_all`이 `No goals to be solved` 및 `Unknown identifier ty2`로 실패 | `PRICE_REQUEST` / 설정 예산 시 `EMIT_LLM_PROMPT` (`mode=repair`, `scope=body`) | 원본 `1670`자 / `5176` HB, gold `1628`자 / `5172` HB | 국소 tactic 수리(`simp?`/`exact?`)만 보고 승인하면 안 되고 반드시 뒤쪽 전체를 replay해야 함을 실제로 보여주는 사례. Gold는 뒤의 죽은 줄까지 함께 정리해 통과. |

### `request.json` vs `request.configured_budget.json` 설명
- 실제 실행 환경에서는 호출할 모델과 토큰 단가표가 지정되지 않았으므로, 기본 `request.json`에는 `cap_usd: null, next_call_upper_bound_usd: null, spent_usd: 0.0`을 기록했습니다. 이에 따라 [`escalation_policy.py`](../escalation_policy.py)는 가격 미확인을 감지하여 `PRICE_REQUEST`를 반환합니다.
- 동시에 프롬프트 렌더링 경로(`EMIT_LLM_PROMPT`)와 `prompt.txt`를 검증하기 위해, 명시적으로 `"source": "CONFIGURED PLACEHOLDER, not a price quote and not a Lean measurement"`라고 표시한 `request.configured_budget.json`과 `decision.configured_budget.json`, `prompt.txt`를 함께 저장했습니다.

---

## 5. 정책 Fixture 요약 (`policy-fixtures/P01`~`P04`)

모든 파일은 `"synthetic": true`를 포함하며 실제 Lean 측정값과 분리되어 있습니다.

- **`P01` (예산 부족 / 가격 상한 미확인, 6건)**: 예산 초과(`a`), 병렬 예약금(`reserved_usd`) 포함 초과(`b`), 단가 상한 `null`/`cap` `null`/음수 상한 시 `PRICE_REQUEST`(`c`~`e`), 정확히 상한과 일치(`<=`)할 때 `EMIT_LLM_PROMPT`(`f`).
- **`P02` (동일 요청 차단 vs 새 정보 / 범위 확대, 8건)**: 동일 요청 반복 시 `REUSE_OR_STOP`(`a`), 같은 candidate hash라도 새 진단 정보가 있으면 허용(`b`), 유효한 `state_certificate`가 있을 때 `tactic` → 동일 실패 시 `block` → `body`로 범위 확대(`c`~`e`), 수리 횟수 한도 도달 시 `SELECT_BEST`(`f`), 로컬 수리 미완료 `RUN_LOCAL`(`g`), 로컬 증거 누락 `COLLECT_EVIDENCE`(`h`).
- **`P03` (환경 오류 / Baseline 미검증 / 불변 계약 및 상태 인증서 검증, 16건)**:
  - `environment_error` → `FIX_ENVIRONMENT`(`a`), `baseline_verified=false` → `VERIFY_BASELINE`(`b`), wrapper 오류(`c`).
  - **2026-10-15 보완 계약**: 결론 값 변경(`answer = 42` → `43`, `d`), 가정 추가(`(h : False)`, `e`), 본문 밖 공백 변경(`f`), 뒤쪽 선언 추가(`g`), `source_contract` 누락(`h` → `CHECK_CONTRACT`), `body_start`/`body_end` 불일치(`i`), runner 위반 플래그(`j`).
  - **상태 인증서 무결성**: 오래된 candidate hash(`k`), 오래된 environment hash(`l`), 인증서 없이 `trusted_pre_state=true`만 준 경우(`m`), 오류 복구 placeholder 사용(`n`), 재실행 digest 불일치(`o`), prefix 오류 존재(`p`) 시 모두 좁은 범위를 거부하고 `scope="body"`로 강제 확대.
- **`P04` (가상 점수 동점·악화·개선·누락·모델 실패 뒤 best 보존, 정책 13건 + selector 12건)**:
  - 정책 게이트(`a`~`m`): 원본과 동점(`a`), 명확한 개선 시 추가 호출 없이 `SELECT_BEST`(`b`), 토큰은 줄었으나 HB가 125% 이상일 때 optimization 호출(`c`), 일부 버전 실패 시 optimization 호출(`d`), HB 누락/버전 미완결/오래된 metric hash/baseline 분모 0/비교 불가/NaN/서술형 `optimization_evidence`만 있는 경우 모두 `MEASURE`(`e`~`k`), 모델 최적화 실패 후 한도 도달 시 `SELECT_BEST`(`l`), 트리거 충족이나 가격 미확인 시 `PRICE_REQUEST`(`m`).
  - 별도 selector 계약 데이터(`selector_contract_cases.json`, `s01`~`s12`): `escalation_policy.py`는 점수 계산/선택기를 구현하지 않으므로, 별도 selector 계약(raw 값 비교, 동점/악화 시 원본 fallback, 표시용 반올림 동점 구분, 미검증 baseline 구분, 모델 실패 뒤 기존 최고점 보존, 단일 축 악화 허용)을 테스트하는 데이터로 분리 제공했습니다.

---

## 6. 한계 및 주의사항

1. **문자열 계약 검사의 한계**: 현재 `immutable_contract`는 `원문 prefix + 후보 body + 원문 suffix` 일치만 검사합니다. 본문 내부에 주석이나 새 선언을 주입해 뒤쪽을 삼키는 공격을 막으려면 Lean adapter의 단일 term/command 보존 및 커널 타입 검사가 추가로 필요하며, 따라서 모든 케이스의 `validation_status`에 `string_contract_only_no_lean_adapter_term_check`를 명시했습니다.
2. **상태 재현 인증서 미구현**: `trace_state`로 수집한 실패 직전 goal은 계측용 수정 파일을 실행해 얻은 관찰값(`trusted=false`)이며 깨끗한 prefix replay digest 인증서가 아닙니다. 따라서 정책 입력에서는 모두 `scope="body"`로 처리됩니다.
3. **계측의 한계**: 공식 Arena tokenizer가 없으므로 `official_tokens`는 전부 `not_measured`로 두었고, 비공백 문자 수(`body_nonwhitespace_chars`)만 `local_estimate`로 기록했습니다. Heartbeat는 `IO.getNumHeartbeats`(`Elab.async=false`) 단일 실행 로컬 추정치이며 공식 워커 측정값이 아닙니다.
4. **버전 호환성(`robustness`) 한계**: `R06`/`R06b`(`Core.InitsUpdatesComm`)는 지정된 3개 버전(`v4.29.1`, `v4.27.0`, `v4.26.0`) 중 로컬에 준비된 `v4.26.0` 1개만 실행했으므로 `robustness_incomplete`로 표시했습니다.
5. **일반화 금지**: 이 9개 Lean 사례와 4개 정책 fixture 묶음은 파이프라인의 회귀/연결 검증용 소규모 데이터이며, 전체 대회 성공률이나 정책의 최적성을 입증하는 근거로 사용할 수 없습니다.
