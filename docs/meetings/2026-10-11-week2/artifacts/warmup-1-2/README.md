# Warm-up 1·2 증명과 재현 자료

## 현재 풀이 — 2026-10-09

- [새 증명](improved_proofs.lean): 공통 목록 결합 성질을 로컬 `combine`으로 증명하고 AST/정규화 증거의 각 경우를 직접 처리한다. 기존 명제와의 동일성도 Lean으로 확인한다.
- [적용 패치](CallElimCorrect.improved.patch): 지정 revision의 두 증명 몸체만 교체한다.
- [측정 원자료](heartbeat-2026-10-09/measurements.json): 원본·기존 압축 후보·새 증명의 3회 측정값, 공리, 크기.
- [측정 도구](measure-heartbeats.cjs): 각 증명을 같은 이름으로 별도 Lean 프로세스에서 새로 처리한다. import를 제외한 동기 선언 elaboration·검사를 `Lean.withHeartbeats`로 측정하고, 내부 계수를 1,000으로 나눈다. 공식 Arena harness는 아니다.
- [표시 내용 확인 도구](check-presentation.cjs): HTML 명제·증명과 검증한 소스의 일치, 소스 크기, 링크 및 순회 예시를 확인한다.

| Heartbeat 중앙값 | 원본 | 이전 압축 후보 | 새 증명 |
| --- | ---: | ---: | ---: |
| 1번 | 5,207.667 | 5,679.793 | 1,105.482 |
| 2번 | 2,612.070 | 2,549.236 | 461.131 |

새 증명의 몸체는 보조 증명을 포함해 23줄/20줄, 공백 제외 769자/533자다. 원본 대비 heartbeat는 약 78.8%/82.3%, 기존 압축 후보 대비 약 80.5%/81.9% 감소했다. 실행 시간이나 다른 버전의 결과로 해석하지 않는다. 모든 측정 대상은 검증에 성공했고 공리는 `[propext, Quot.sound]`다.

모듈 전체에 새 증명을 적용한 `lake build Strata.Transform.CallElimCorrect`와 `lake env lean improved_proofs.lean`을 2026-10-09에 실행해 통과했다. 다른 선언의 기존 `sorry` 경고는 있으나 두 대상 정리에는 `sorryAx` 의존성이 없다. 초기 실험에서 `grind` 기반 후보는 추가 공리 의존성이 발생해 채택하지 않았다.

### 새 풀이 재현

Strata revision `451e5f047bafa010d178856db76c00029bfa4d7f`의 별도 checkout과 `leanprover/lean4:v4.26.0`을 사용한다. 아래 `/path/to/artifacts`를 이 폴더의 실제 경로로 바꾼다. 이전 패치와 새 패치를 중복 적용하지 않는다.

```sh
git apply /path/to/artifacts/CallElimCorrect.improved.patch
lake build Strata.Transform.CallElimCorrect
lake env lean /path/to/artifacts/improved_proofs.lean
node /path/to/artifacts/measure-heartbeats.cjs /path/to/Strata /path/to/lake /path/to/output
node /path/to/artifacts/check-presentation.cjs
```

이번 Windows 환경의 Lean은 기존 elan에 v4.26.0을 추가해 사용했다. 설치 위치는 `C:/Users/남성우닮은박보검/.elan/toolchains/leanprover--lean4---v4.26.0/bin`이며, 격리된 Strata checkout은 이 저장소의 `.warmup-work/strata`에 있다. 다른 PC에서는 해당 경로 대신 자신의 `lake`를 지정한다.

## 이전 기록 — 2026-10-06

- [최초 HTML 보고서](warmup_problems_1_2_report.html): 토큰·tactic 수치는 재검증되지 않았으므로 공식 점수로 사용하지 않습니다.
- [검증 기록](warmup_1_2_verification.json): 2026-10-06 검증 환경, 소스 크기, 원본·후보 공리 목록. heartbeat와 다른 버전은 미측정입니다.
- [증명 변경 패치](CallElimCorrect.patch): 두 정리의 명제를 유지하고 증명 몸체만 변경합니다.
- [원본 비교·공리 검사 파일](verify_warmup_1_2.lean): 패치한 모듈을 import하고 원본 증명을 별도 이름으로 재검증합니다.

### 이전 풀이 재현

Strata 저장소의 revision `451e5f047bafa010d178856db76c00029bfa4d7f` 및 Lean v4.26.0 기준입니다. 해당 revision의 별도 checkout에서 패치를 적용합니다. 아래 경로는 이 자료의 실제 위치로 바꿉니다.

```sh
git apply /path/to/warmup-1-2/CallElimCorrect.patch
lake build Strata.Transform.CallElimCorrect
lake env lean /path/to/warmup-1-2/verify_warmup_1_2.lean
```

빌드와 공리 검사는 검증 기록 작성 시 수행한 결과입니다. 자료 보관을 위한 이번 커밋에서 Lean 검증을 다시 실행하지는 않았습니다. 다른 선언의 기존 `sorry` 경고와 두 대상 정리의 공리 검사는 구분해야 합니다.
