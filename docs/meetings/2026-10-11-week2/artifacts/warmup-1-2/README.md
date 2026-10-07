# Warm-up 1·2 원본 결과와 재현 자료

- [최초 HTML 보고서](warmup_problems_1_2_report.html): 토큰·tactic 수치는 재검증되지 않았으므로 공식 점수로 사용하지 않습니다.
- [검증 기록](warmup_1_2_verification.json): 2026-10-06 검증 환경, 소스 크기, 원본·후보 공리 목록. heartbeat와 다른 버전은 미측정입니다.
- [증명 변경 패치](CallElimCorrect.patch): 두 정리의 명제를 유지하고 증명 몸체만 변경합니다.
- [원본 비교·공리 검사 파일](verify_warmup_1_2.lean): 패치한 모듈을 import하고 원본 증명을 별도 이름으로 재검증합니다.

## 재현

Strata 저장소의 revision `451e5f047bafa010d178856db76c00029bfa4d7f` 및 Lean v4.26.0 기준입니다. 해당 revision의 별도 checkout에서 패치를 적용합니다. 아래 경로는 이 자료의 실제 위치로 바꿉니다.

```sh
git apply /path/to/warmup-1-2/CallElimCorrect.patch
lake build Strata.Transform.CallElimCorrect
lake env lean /path/to/warmup-1-2/verify_warmup_1_2.lean
```

빌드와 공리 검사는 검증 기록 작성 시 수행한 결과입니다. 자료 보관을 위한 이번 커밋에서 Lean 검증을 다시 실행하지는 않았습니다. 다른 선언의 기존 `sorry` 경고와 두 대상 정리의 공리 검사는 구분해야 합니다.
