# Warm-up 14·15 로컬 측정 (전체 `import Mathlib`, v4.26.0)

- 작성: 박채원, Week 3 모임(2026-10-18) 공유
- 측정일: 2026-10-16
- 근거 파일: [evidence/local-v4.26/](evidence/local-v4.26/)

## 1. 무엇을 측정했나

Warm-up 14 `putnam_1964_b2`와 15 `putnam_1995_a3`의 대회 참조 증명과 내 증명(Week 2 제출, [report.md](report.md))을 같은 환경에서 컴파일했다. 각 증명에서 다음을 기록했다.

- 컴파일 성공 여부
- `#count_heartbeats`
- `#print axioms`
- 공식 `proof_length` 방식의 proof token 수

## 2. 환경

- Lean v4.26.0 + Mathlib v4.26.0 (`lean-toolchain`, `lakefile.toml`). v4.26.0은 14번(v4.25.0, v4.26.0)과 15번(v4.25.0, v4.26.0, v4.27.0) 모두의 지정 toolchain이다.
- 대회 헤더와 같은 `import Mathlib`, `import Aesop`
- 측정용 옵션: `set_option maxHeartbeats 100000000`, `set_option Elab.async false`, 정리 앞 `#count_heartbeats in`, 파일 끝 `#print axioms`
- Windows 개인 PC, VS Code Lean 4 확장 Infoview에서 값을 읽음
- proof token: `tools/count_tokens.py` (공식 `proof_length` 재구현 `proof_tokens.py` 사용)
- 저장소 규칙(`git diff --check`)에 맞추려고, 측정 뒤 `.lean` 파일의 줄 끝 공백을 지웠다. 증명 내용과 proof token 수는 같다. 공백을 지운 파일로 heartbeat를 다시 재지는 않았다.

## 3. 결과

| 문제 | 증명 | 파일 | proof token | `#count_heartbeats` | 컴파일 | `#print axioms` |
| --- | --- | --- | ---: | ---: | --- | --- |
| 14 | 참조 | `P14_ref.lean` | 1,754 | 134,483 | 성공 | `[propext, Classical.choice, Quot.sound]` |
| 14 | 내 증명 | `P14_mine.lean` | 364 | 1,703 | 성공 | `[propext, Classical.choice, Quot.sound]` |
| 15 | 참조 | `P15_ref.lean` | 4,085 | 14,306 | 성공 | `[propext, Classical.choice, Quot.sound]` |
| 15 | 내 증명 | `P15_mine.lean` | 283 | 2,111 | 성공 | `[propext, Classical.choice, Quot.sound]` |

- heartbeat 단위는 `#count_heartbeats` 출력 그대로(`Used … heartbeats`)다.
- 15번 참조 증명의 Infoview 메시지 전체: [P15_ref.infoview.txt](evidence/local-v4.26/P15_ref.infoview.txt)
  - 린터 경고 `this tactic is never executed` 16개
  - `tactic does nothing` 16개
  - `This simp argument is unused` 3개
  - `<;>` 불필요 2개

## 4. 점수에 대해

이 문서에는 점수를 적지 않는다. 대회 점수는 Arena에 제출해 받은 공식 채점 값만 사용한다. 공식 Scoring 정의는 대회 Home의 "How scoring works"를 따른다.

> Every accepted proof is scored on two reduction axes and a cross-version transfer check. The default rank — combined % — is the mean of all three; rows that fail to compile, change the statement, or contain sorry score zero.

이번 측정은 v4.26.0 하나에서만 했다. 다른 지정 toolchain(v4.25.0, 15번은 v4.27.0)에서는 이 환경으로 확인하지 않았다.

## 5. 재현

```powershell
cd evidence\local-v4.26
lake update
lake exe cache get
# VS Code로 각 .lean 파일을 열고 #count_heartbeats, #print axioms 결과를 Infoview에서 확인
python tools\count_tokens.py tools\statement14.lean P14_ref.lean P14_mine.lean
python tools\count_tokens.py tools\statement15.lean P15_ref.lean P15_mine.lean
```
