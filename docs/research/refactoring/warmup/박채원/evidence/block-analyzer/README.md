# Warm-up 블록 분석기

Warm-up 15문제의 참조 증명을 블록으로 나누고 블록별 proof token을 센다. 결과는 [blocks.md](blocks.md), 같은 내용의 JSON은 [blocks.json](blocks.json)이다.

## 규칙

1. 증명 최상위의 tactic 하나와 그 아래 들여쓴 줄을 블록 하나로 본다.
2. 블록 하나가 전체 토큰의 80% 이상이고 안쪽 줄이 있으면 그 안으로 내려가 다시 나눈다. 15번 `h_main`이 그 예다.
3. 40토큰 이상인 블록(깊이 무관)끼리 변수명을 정규화해 비교하고, 유사도 0.9 이상을 반복 논증 후보로 적는다.
4. `case tag =>`, `| tag =>` 분기 본문(8토큰 이상)끼리 같은 방식으로 비교하고, 유사도 0.85 이상을 후보로 적는다.
5. 최상위 블록을 `case` 분기, `calc` 단계, `have` 계열, 기타로 나누고 토큰 비중이 50% 이상인 종류로 증명 유형(분기형, 계산 연쇄형, 중간 명제형, 혼합형)을 정한다.
6. 전체의 40% 이상인 블록은 같은 들여쓰기 규칙으로 한 단계 더 나눈다.

반복 후보는 토큰열이 비슷하다는 뜻이며 같은 논증이라는 증명은 아니다. 유형 분류 결과와 유형별 분할 규칙은 [blocks.md](blocks.md) 앞부분에 있다.

## 확인

- 토큰은 [proof_tokens.py](../local-v4.26/tools/proof_tokens.py)로 센다. 문제마다 블록 합과 `:= by` 줄 토큰의 합이 공식 `proof_length`와 같은지 확인하며, 15문제 모두 같다.
- heartbeat는 재지 않았다. 1–12번은 문제별 저장소와 지정 버전 환경이 필요하다.

## 실행

```bash
cd docs/research/refactoring/warmup/박채원/evidence/block-analyzer
python block_analyzer.py <benchmark_data_warmup.jsonl> --md blocks.md --json blocks.json
```

`benchmark_data_warmup.jsonl`은 Lean Refactor Arena에서 내려받은 Warm-up 데이터다.
