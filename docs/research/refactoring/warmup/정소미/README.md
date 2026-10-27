# 정소미 Warm-up · 증명 최적화와 검증

Warm-up 증명의 리팩터링·평가 기록입니다. 2026-10-11 Week 2에는 담당 P04·P09의 증명 수정 과정을, 2026-10-18 Week 3에는 후보 선택·실패 집계 방식에 따른 평가 차이를 다뤘습니다. 2026-10-26에는 15문제의 증명을 수정하며 측정한 결과와 지정 버전 검증을 정리했습니다.

- [2026-10-26 · 15문제 증명 수정과 측정 기록](optimization-20261026.md): 후보 65개의 결과, 토큰·HB 비교와 버전 검증.
- [15문제 실험 코드와 실행 방법](evidence/warmup15-20261026/README.md): 후보 생성·검증 명령과 로그.

- [Week 3 발표자료 · 후보 선택과 실패 집계](evaluation.html): 16장. 담당 영역과 참고 논문, 평가 결과, 실행 모듈과 새 후보 생성·수정 결과.
- [Week 3 상세 보고서](reproducibility.md): 기존 후보 28개 재평가와 새 후보 생성·수정 실행을 별도로 정리.
- [Week 3 평가 방법 실험과 근거](evidence/method-comparison/README.md): 고정 후보·환경, 실행 코드, 원시 결과와 표 재생성.
- [Lean 평가 도구와 에이전트 실행 모듈](evidence/tool-harness/README.md): Codex CLI·MCP를 통한 새 후보 평가, 오류 수정과 선택. 4번 2시도·0유효, 9번 3시도·1유효.
- [공통 프롬프트 및 제공자별 입력 형식](evidence/tool-harness/prompt_pack.py): META·CREATE·REPAIR 분리와 OpenAI·Claude·Gemini용 프롬프트 필드 내보내기. 제공자별 SDK 직접 호출은 포함하지 않음.
- [기초 반복 실행과 근거](evidence/reproducibility/README.md): 고정 조건, 실행 도구, 결과 표, 환경 기록과 Lean 출력.

- [Week 2 발표자료](presentation.html): 4·9 실험과 Lean Refactor 및 관련 논문 조사를 함께 담습니다.
- [Week 2 상세 보고서](report.md).
- [증명·시도·로그·재현 스크립트](evidence/): `P4/`, `P9/`와 Python 도구.
- [별도 Lean Refactor 논문 문서](../../../verifier-guided-agent/정소미/report.md).

Week 2 슬라이드는 Verifier-guided Agent 폴더에서도 연결합니다. Week 3는 위 HTML을 대표 발표자료로 사용하고, 상세 조건과 원시 결과는 보고서에서 확인합니다.
