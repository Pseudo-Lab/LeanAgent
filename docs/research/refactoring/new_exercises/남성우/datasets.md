# 연습 세트와 실행 기록의 구분

원본 커밋에서 가져온 JSONL의 실제 레코드 수입니다. 파일 간 중복이 있어 합계를 고유 문제 수로 해석하지 않습니다. 별도 테스트용 세트는 minimizer A에서 전부 평가하지 않았으며 발표자료의 15문제 성적은 Warm-up 개발 세트 결과입니다.

| 파일 | 레코드 수 |
| --- | --- |
| [arena_practice_benchmark.jsonl](evidence/validation-mini/arena_practice_benchmark.jsonl) | 15 |
| [lean_refactor_eval_analysis_warmup_format.jsonl](evidence/validation-mini/lean_refactor_eval_analysis_warmup_format.jsonl) | 10 |
| [pre_refactor_by_case_warmup_format.jsonl](evidence/validation-mini/pre_refactor_by_case_warmup_format.jsonl) | 9 |
| [pre_refactor_seeds_warmup_format.jsonl](evidence/validation-mini/pre_refactor_seeds_warmup_format.jsonl) | 6 |
| [strata_local_practice_warmup_format.jsonl](evidence/validation-mini/strata_local_practice_warmup_format.jsonl) | 10 |

실제로 실행한 소규모 검증은 [validation-mini 사례 표](evidence/validation-mini/README.md), 기존 15문제 후처리 평가는 [minimizer 결과](report.md)에서 확인합니다. 원본 JSONL·증명·측정값을 변경하지 않았습니다.
