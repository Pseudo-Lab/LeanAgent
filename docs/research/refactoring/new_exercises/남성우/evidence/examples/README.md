# 모델 없는 Lean 예제

`non_llm_core.lean`의 15개 example을 Strata checkout의 Lean v4.26.0에서 검사했다. 명령: `lake env lean /path/to/non_llm_core.lean`, exit 0. 모델 API 호출 없이 실행했다.

검사일: 2026-10-13. import Lean만 사용하는 작은 예제다. exact?와 simp?는 일반 proof script를 제안한다. 이 예제 검증은 Arena 공식 token/heartbeat 측정이나 실제 대상 정리의 refactoring 성능 검증을 대신하지 않는다.

설명에서 다루는 Mathlib의 ring/linarith 및 Aesop 예제는 이 파일의 실행 범위에 포함하지 않는다.
