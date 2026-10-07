# Nagata 형식화 학습 자료

OpenAI `math`의 평면곡선 Nagata 개발을 읽고, Lean 리팩터링에 재사용할 교훈을 정리한 자료입니다.

- [발표용 HTML](presentation.html): 핵심 takeaway 9장, 화살표 이동, 발표 메모, 인쇄 지원. 브라우저에서 파일을 열어 사용합니다.
- [개인 공부용 상세 분석](extensive-analysis.md): 문제 해석, 양화사, 표현과 bridge, 증명 구조, 읽기 순서, 연습문제, 남은 검증.
- [소스 관찰 기록](source-audit.json): 고정 revision, 환경, import 목록, 키워드 검색, 파일 해시.
- [관찰 재현 스크립트](scan_sources.py): Python 표준 라이브러리만 사용. Lean 검사기를 대신하지 않습니다.

검토 revision: `adc7f1241b42e322a6451854ab7e4b4c146bf78a` · 2026-10-07.

이 자료는 주요 소스의 정적 검토입니다. 고정된 Lean 환경의 빌드, 실제 공리 출력, Comparator 실행은 미수행입니다. 논문의 전체 수학적 증명을 독립적으로 검증했다는 뜻이 아닙니다.
