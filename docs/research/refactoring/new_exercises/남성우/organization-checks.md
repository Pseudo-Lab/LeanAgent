# 문서 정리 검증 기록

2026-10-23 · 원본 커밋 98e945c · 2026-10-25 미팅 준비.

- 코드·증명·측정·로그 등 MD/HTML 이외 4,050개 파일: 원본 SHA-256와 일치.
- 추가·이동된 문서의 상대 파일 링크 68개: 깨진 링크 0개.
- minimizer 단위 테스트 10개 통과 (`python -X utf8 -m unittest discover`).
- 정책 fixture 43개와 selector 계약 12개 통과 (`python -X utf8 policy_fixture_check.py`).
- Windows 기본 cp949 입력 오류는 UTF-8 모드로 해결. 테스트 임시 폴더는 쓰기 가능한 작업 폴더로 지정.
- HTML 브라우저 로딩·발표 모드·다음/이전 및 Home/End 탐색 확인.
- Lean 전체 재실행 및 공식 Arena 제출은 수행하지 않음. 기존 실행 기록을 보존하고 Python 검증과 문서 점검만 수행.

원본 파일별 경로·해시는 [provenance.json](provenance.json)에 있습니다.
