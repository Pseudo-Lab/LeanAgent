# 손지연 검증·수리 실험 요약

2026-10-18 Week 3 공유 자료. 기존 실행 자료를 문서와 JSON으로 요약했습니다. 원본 증명·실행 코드·로그·환경 및 소스 사본은 이 폴더에서 삭제했습니다.

- 대표 보고서: [검증·수리 설계와 실행 (HTML)](../report.html).
- 측정 목차: [metrics.json](metrics.json).
- 요약 대조·정리 검사: [validation.json](validation.json).

| 실험 | 문서 | JSON | 확인된 범위 |
| --- | --- | --- | --- |
| 작은 REPL 예제 | [설명](repl/README.md) | [결과](repl/results.json) | 고정 후보·12개 요청, 모델 미호출 |
| P7·P12 통제 실험 | [설명](controlled/README.md) | [결과](controlled/results.json) | 정상·오류·알려진 수정의 전체 파일 검증 |
| P7 모델 후보 | [설명](model-repair/README.md) | [결과](model-repair/results.json) | 첫 실제 후보 한 건 무수정 적용·최종 통과 |
| 회귀·parser 시험 | [설명](tests/README.md) | [결과](tests/results.json) | 회귀 22개(controller 13개 포함), 별도 parser 15개 |

각 JSON은 실행 환경·식별자·측정값·판정·한계와 주요 원본의 SHA256을 남깁니다. `provenance.original_relative_path`는 삭제된 원본을 식별하는 과거 경로이며 현재 파일 링크가 아닙니다.

이 자료는 결과 공유용 요약입니다. 원시 파일을 삭제했으므로 요약본만으로 전체 실험을 재실행하거나 원시 응답·로그를 재감사할 수 없습니다. 새 Lean 검증·모델 호출·시험은 수행하지 않았습니다.

[문서 지침](../../../../../STRUCTURE.md)과 [PR #16의 주제별 근거 자료 구성](https://github.com/Pseudo-Lab/LeanAgent/pull/16)을 참고했습니다.
