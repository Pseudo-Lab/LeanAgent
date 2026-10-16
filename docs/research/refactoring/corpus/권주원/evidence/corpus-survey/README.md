# 코퍼스 통계의 입력과 재현 방법

대표 문서는 [report.html](../../report.html)입니다. 이 폴더는 집계 수치와 재현 코드를 보관합니다. 대용량 원시 코퍼스와 레코드 압축 파일은 이 커밋에 포함하지 않습니다.

## 1. 저장된 통계로 보고서 재생성

LeanAgent 저장소 루트에서 실행합니다. Python 3.9 이상과 표준 라이브러리만 필요합니다.

```bash
python3 docs/research/refactoring/corpus/권주원/evidence/corpus-survey/build_report.py --render-only
```

포함된 `analysis.json`을 읽어 `../../report.html`과 `source-summary.csv`를 재생성합니다. 원시 입력·Lean·모델 호출이 필요하지 않습니다. 이 모드는 통계를 새로 계산하거나 검증하지 않습니다. 설명과 스타일은 `report-template.html`에서 수정합니다.

## 2. 원본 집계 레코드로 전체 통계 재계산

입력 스냅샷 커밋은 `b740bc5172c4d292b0bad1199ac550a0c56a38e5`입니다. 해당 스냅샷의 results 압축 묶음을 별도 위치에 복원한 `corpus/results/`를 사용합니다. 필요한 파일은 다음과 같습니다.

```text
results/
├── all_sources/
│   ├── summary.json
│   ├── verification.json
│   └── declarations.jsonl.gz
├── proof_lengths/
│   ├── summary.json
│   ├── validation.json
│   └── lengths.jsonl.gz
└── warmup_candidates/
    └── summary.json
```

`analysis.json`의 `input_sha256`은 다섯 주요 입력의 해시를 보존합니다. 기존 검증 JSON의 해시와 요약값도 대조합니다. 현재 알려진 해시와 다른 임의의 최신 코퍼스를 같은 실험 입력으로 간주하지 않습니다.

```bash
python3 docs/research/refactoring/corpus/권주원/evidence/corpus-survey/build_report.py \
  --results-root /absolute/path/to/corpus/results
```

길이 레코드 380,489개에서 30개 히스토그램을 재구성하고, 6개 출처의 선언 레코드 382,121개를 대조합니다. 주 모집단의 증명 문자열 중복, 파일 집중도, 출처별 가중 민감도를 다시 계산하고 JSON·CSV·HTML을 갱신합니다. 입력 파일은 수정하지 않습니다. 원문에서 토큰을 다시 세거나 Lean 검증을 실행하는 절차는 아닙니다.

입력 파일을 준비하지 않은 새 clone에서도 모드 1로 보고서를 재생성할 수 있습니다. 모드 2에는 위 별도 입력이 필요하며, 입력 없이 전체 재분석을 재현했다고 주장하지 않습니다.

## 파일과 검증 범위

| 파일 | 역할 |
| --- | --- |
| [analysis.json](analysis.json) | 기존 보고서와 동일한 통계, 모집단·방법·입력 SHA-256 |
| [source-summary.csv](source-summary.csv) | 출처별 주요 수치 |
| [build_report.py](build_report.py) | 저장 통계 렌더링 또는 지정 입력의 재집계 |
| [report-template.html](report-template.html) | 공유 보고서를 생성하는 HTML 템플릿 |
| [validation.json](validation.json) | 이전 검증 기록과 이관 후 검증을 구분한 기록 |

2026-10-16 원본 보고서 작성 시 기존 Python 검사 43개, 입력 해시, 재생성 바이트 일치와 브라우저 조작을 확인했습니다. 그 기록은 `validation.json`의 `source_validation`에 보존합니다. 이관 후 검증은 `leanagent_migration`에 따로 기록합니다. 직접 파일 열기의 브라우저 자동화와 PDF 실제 출력은 미검증이며, HTML 화면·조작은 localhost에서 확인합니다.

문자열 동일성은 같은 문제나 의미적으로 같은 증명이라는 뜻이 아닙니다. 직접 sorry 제외는 전이적 공리 검증을 대신하지 않으며, 이번 실행에서 새 Lean 검증·heartbeat 측정·모델 생성은 수행하지 않습니다.
