# Warm-up 14·15: 참조 증명은 어디서 길어졌나

- 작성: 박채원 (구조/전략 설계 그룹), Week 3 모임(2026-10-18) 공유
- 근거 파일: [evidence/local-v4.26/](evidence/local-v4.26/) (Lean 파일과 토큰 계산 스크립트)

## 1. 이번 주 작업

Week 2에 14·15번 참조 증명을 짧게 고쳐 썼다([report.md](report.md)). 이번에는 참조 증명의 어느 부분이 길었는지, 수정한 증명에서 그 부분이 어떻게 바뀌었는지를 proof token으로 비교했다. 증명을 `have` 블록 단위로 나눠 세었다.

## 2. proof token을 센 방법

- 대회의 proof token은 Lean Refactor 논문 부록 J의 `proof_length` 함수로 센다. 증명 부분(`:=` 뒤)에서 주석과 빈 줄을 지우고, 공백과 기호로 쪼갠 조각 수를 줄마다 세어 더한다.
- 이 함수를 다시 구현한 [proof_tokens.py](evidence/local-v4.26/tools/proof_tokens.py)로 셌다. 웜업 15문제의 공식 `proof_length` 값을 모두 똑같이 재현한다.
- 참조 증명의 토큰(14번 1,754, 15번 4,085)은 대회 데이터의 공식 `proof_length` 값과 같다. 수정한 증명의 토큰(364, 283)은 같은 재구현으로 센 값이고, 공식 값은 Arena 제출로만 확인된다.
- 줄마다 세어 더하므로, 줄 범위별로 나눠 센 값에 첫 줄 끝의 `by` 1개를 더하면 전체와 같다. 블록별 값은 [block_tokens.py](evidence/local-v4.26/tools/block_tokens.py)로 셌고, 네 파일 모두 합이 전체와 일치한다.
- 이 문서는 proof token만 다룬다. heartbeat는 공식 채점 환경과 같은 값인지 확인할 수 없어서 넣지 않았다.

## 3. 14번 `putnam_1964_b2` (1,754 → 364)

| 참조 블록 (줄) | 토큰 | 수정한 증명에서 | 토큰 |
| --- | ---: | --- | ---: |
| `h_no_empty` (16–21) | 58 | 없음. 뒤에서 쓰이지 않는 사실이었다 | 0 |
| `h_subset_or_compl` (23–135), `h_not_both` (137–147) | 818 | `key : T ∈ P ↔ Tᶜ ∉ P` 하나로 합침 (16–49) | 201 |
| `h_card` 안 `Q`, `card_bij'`, 합집합 (149–267) | 591 | `P.image compl`과 Mathlib 정리 `Finset.card_image_of_injective` (50–68) | 128 |
| `h_card` 안 마지막 산술 (269–303) | 286 | `Nat.exists_eq_succ_of_ne_zero`, `omega` (69–74) | 34 |

- "T ∈ P 또는 Tᶜ ∈ P"와 "둘 다는 아니다"를 따로 증명하던 것을 `↔` 하나로 묶었다.
- `h_subset_or_compl` 안에는 A와 Aᶜ에 대해 같은 논증이 두 번(29–64, 66–101, 각 256 토큰) 있었다. 수정한 증명에서는 `by_contra`로 각 3줄(합 72 토큰)이 되었다.

## 4. 15번 `putnam_1995_a3` (4,085 → 283)

| 참조 블록 (줄) | 토큰 | 수정한 증명에서 | 토큰 |
| --- | ---: | --- | ---: |
| `h_main`, `h₁`–`h₄` (16–25) | 235 | `intro`, `obtain`, `subst` (16–20) | 40 |
| `h₅` (27–74), `h₆` (76–123) | 1,624 | 보조정리 `key` 하나 + `simp only [key]` (21–27) | 135 |
| `h₇` (125–198), `h₈` (200–231) | 1,681 | `hS`, `h3` (28–35) | 89 |
| `h₉` (233–286), 끝 (288–291) | 544 | `IsCoprime.pow_right` 한 줄 (36–37) | 18 |

- `h₅`와 `h₆`는 (d, e)와 (e, f)만 다른 같은 논증이고 각 812 토큰이다. 두 블록이 참조 증명의 40%다.
- `h_main`과 `h₁`–`h₄`는 목표와 가정을 이름만 바꿔 다시 적은 것이다.
- `h₉`는 "7은 소수이고 10ⁱ을 나누지 않는다"를 손으로 증명했다. 수정한 증명은 7과 10이 서로소라는 Mathlib 정리를 썼다.

## 5. 두 문제에서 공통으로 본 것

1. **같은 논증의 반복**이 가장 컸다. 15번 `h₅`·`h₆`, 14번 A와 Aᶜ에 대한 두 블록.
2. **Mathlib에 있는 사실을 손으로 증명**한 블록이 컸다. 14번 개수 세기와 산술, 15번 소수 부분.
3. **명제를 다시 적기만 하는 `have`**가 있었다. 14번 `h_no_empty`(쓰이지 않음), 15번 `h_main`과 `h₁`–`h₄`.
4. 수정한 증명에서 토큰이 가장 많은 곳은 풀이의 핵심 명제였다. 14번 `key` 201, 15번 `key`와 그 사용 135.

이 차이는 tactic 하나를 바꾸는 수준이 아니라, 어떤 중간 사실을 세울지 정하는 단계에서 생겼다.

## 6. 구조 설계에 가져갈 점

- 후보를 볼 때 증명 전체가 아니라 **블록 단위로 토큰을 나눠 보면**, 어디를 바꿔야 하는지 바로 보인다. 15번은 가운데 네 블록(`h₅`–`h₈`)이 4,085 중 3,305다.
- Lean 린터 경고(`this tactic is never executed`, `tactic does nothing`, `This simp argument is unused`)는 tactic이나 simp 인자 단위다. 쓰이지 않는 `have` 블록이나 반복 논증 같은 블록 단위 문제는 따로 찾아야 한다.
- 후보는 컴파일되고, 명제가 같고, `sorry`가 없어야 0점을 피한다. 지정 버전 중 그대로 컴파일되는 비율은 zero-shot %로 따로 점수에 들어간다 (아래 Arena 정의).

## 출처

- 채점 정의: Lean Refactor Arena Home "How scoring works", https://huggingface.co/spaces/delta-lab-ai/lean-refactor-arena (2026-10-16 확인). "rows that fail to compile, change the statement, or contain sorry score zero."
- proof token: Lean Refactor 논문 arXiv:2605.20244v2 부록 J의 `proof_length`.
- 린터 정의: `linter.unreachableTactic` (Batteries `Batteries/Linter/UnreachableTactic.lean`), `linter.unusedTactic` (Mathlib `Mathlib/Tactic/Linter/UnusedTactic.lean`), `linter.unusedSimpArgs` (Lean v4.26.0 `src/Lean/Elab/Tactic/Simp.lean`)의 설명문.
