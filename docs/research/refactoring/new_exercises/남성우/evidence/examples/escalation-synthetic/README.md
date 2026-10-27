# 프롬프트 출력 예제 — 합성 정책 fixture

이 폴더의 budget, baseline_verified, diagnostics, local 결과는 정책 분기를 시험하는 **합성 입력**이다. 실제 Lean 수리 실패나 실측 score를 보여주는 예가 아니다. 실제 로컬 자동화는 이 작은 정리를 쉽게 해결할 수 있다.

`request.json` → `decision.json` 및 `prompt.txt`는 실제 Python renderer로 생성했다. request의 gold_repair sentinel은 prompt에 포함되지 않는다. API 호출은 없다.

verifier-guided-agent 폴더에서:

```sh
python3 escalation_policy.py examples/escalation-synthetic/request.json
python3 -m unittest -v test_escalation_policy.py
```

실제 통합 데이터는 Gemini 요청서대로 Lean 관찰값을 수집하여 별도로 제작한다.
