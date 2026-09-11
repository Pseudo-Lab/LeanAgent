<h1 align="center">LeanAgent</h1>

<p align="center">
  <strong>LLM이 만든 수학 증명을 Lean으로 검증하고 개선합니다.</strong>
</p>

<p align="center">
  <a href="https://pseudo-lab.com"><img src="https://img.shields.io/badge/PseudoLab-S13-3776AB" alt="PseudoLab S13"></a>
  <a href="https://lean-lang.org"><img src="https://img.shields.io/badge/Lean-4-0F4C81" alt="Lean 4"></a>
  <img src="https://img.shields.io/badge/Python-3.x-3776AB" alt="Python 3.x">
  <img src="https://img.shields.io/badge/License-MIT-green" alt="MIT License">
  <a href="https://discord.gg/EPurkHVtp2"><img src="https://img.shields.io/badge/Discord-PseudoLab-5865F2" alt="PseudoLab Discord"></a>
</p>

<p align="center">
  <a href="https://github.com/Pseudo-Lab/LeanAgent/stargazers"><img src="https://img.shields.io/github/stars/Pseudo-Lab/LeanAgent" alt="GitHub stars"></a>
  <a href="https://github.com/Pseudo-Lab/LeanAgent/forks"><img src="https://img.shields.io/github/forks/Pseudo-Lab/LeanAgent" alt="GitHub forks"></a>
  <a href="https://github.com/Pseudo-Lab/LeanAgent/issues"><img src="https://img.shields.io/github/issues/Pseudo-Lab/LeanAgent" alt="GitHub issues"></a>
  <a href="https://github.com/Pseudo-Lab/LeanAgent/pulls"><img src="https://img.shields.io/github/issues-pr/Pseudo-Lab/LeanAgent" alt="GitHub pull requests"></a>
</p>

## 🔍 프로젝트 소개

수학 문제를 푸는 AI가 제시한 증명은 어떻게 실제로 검증할 수 있을까요?

[Lean](https://lean-lang.org)은 수학적 명제와 증명을 형식 언어로 표현하고, 작성된 증명이 올바른지를 기계적으로 검사하는 정리 증명 도구입니다. LLM의 아이디어 생성 능력과 Lean의 엄밀한 검증 능력을 결합하면, 답을 한 번 생성하는 데서 끝나지 않고 오류를 발견하고 수정하며 기계적으로 검증 가능한 증명을 만들 수 있습니다.

2026년 9월 8일 OpenAI는 약 1만 개의 동시 에이전트를 활용해 3차원 비압축성 Navier–Stokes 방정식에서 유한 시간 특이점이 형성됨을 보이는 분석적 증명을 제시했다고 발표했습니다. 자연어 증명뿐 아니라 Lean 4로 형식화한 증명 인증서도 공개했으며, OpenAI 발표에 따르면 Lean 형식화와 검증에는 GPT‑6 Astra를 이용해 추가로 17시간이 소요됐습니다. 자세한 내용은 [OpenAI 공식 발표](https://openai.com/index/navier-stokes-solution/)에서 확인할 수 있습니다.

이 사례는 수학적 추론 능력만큼 AI가 만든 결과를 형식화하고 검증하는 과정도 중요하다는 점을 보여줍니다. 실제 시스템에는 증명 계획과 코드 생성뿐 아니라 Lean 오류를 분석하고, 다음 시도를 선택하고, 제한된 실행 예산을 관리하는 구조가 필요합니다.

LeanAgent에서는 다음 과정을 수행하는 에이전트를 직접 구현합니다.

```text
문제 이해 → 증명 계획 → Lean 코드 생성 → 검증 → 오류 분석 → 수정 → 증명 완성
```

### 🧪 우리가 확인하려는 것

**Problem Statement**

> “수학 문제를 푸는 LLM이 그럴듯한 증명을 생성하더라도, 검증 피드백을 이용해 오류를 수정하고 제한된 실행 예산 안에서 증명을 완성하는 재현 가능한 구조가 부족하다.”

LeanAgent는 다음 질문을 실험적으로 살펴봅니다.

> Lean의 검증 피드백을 활용한 에이전트 구조는 수학적 추론의 정확성과 효율을 얼마나 개선할 수 있을까?

## 🎯 이번 시즌 목표

- [ ] Lean과 LLM 기반 자동 정리 증명 연구의 주요 흐름을 이해합니다.
- [ ] Lean 검증 피드백을 다음 시도에 반영하는 LeanAgent를 구현합니다.
- [ ] 동일한 문제와 실행 예산에서 여러 증명 생성·수정 방식의 성능과 효율을 비교합니다.
- [ ] 논문의 핵심 정리나 증명 일부를 LeanAgent로 검토하는 research use case를 만들고 공유합니다.
- [ ] 코드, 실험 결과, 문서와 예제를 재현 가능한 형태로 GitHub에 공개합니다.
- [ ] NeurIPS Workshop Lean Refactor Arena Track 1에 참여합니다.

### 📦 주요 결과물

- `Lean Environment & Benchmark` — 공통 Lean 환경과 기본 문제 세트
- `Evaluation Harness` — 모델 호출, Lean 검증, 실행 기록과 비용 계산을 연결한 실험 도구
- `LeanAgent` — 검증 결과를 바탕으로 다음 시도를 결정하는 에이전트
- `Research & Experiment` — baseline 비교 실험, 실패 유형 분석과 technical report
- `Research Use Case` — 새로운 정리와 연구 속 작은 수학적 주장에 대한 검증 사례
- `Open Source Repository` — 코드, 설정, 결과와 재현 방법을 담은 공개 저장소

Lean Refactor Arena에는 proof repair 및 proof engineering 능력을 시험하는 응용 트랙으로 참여합니다. 대회 이후에는 harness와 에이전트를 새로운 정리 증명과 연구 속 수학 검증으로 확장합니다.

## 🔁 실험 방식

```text
Explore → Design → Build → Test → Improve → Share
```

- 작은 단위로 구현하고 실제 Lean 실행 결과로 확인합니다.
- 성공한 결과뿐 아니라 실패한 시도와 수정 과정도 기록합니다.
- 비교 실험에서는 같은 문제, 모델과 실행 예산을 사용합니다.
- 성공률과 함께 비용, 실행 시간, 검증 횟수, 안정성과 오류 유형을 분석합니다.
- 각자 담당한 코드, 실험 또는 문서 결과물을 끝까지 완성하고 서로 리뷰합니다.

프로젝트 결과는 오픈소스로 공개하는 것을 원칙으로 합니다. 다만 Lean Refactor Arena 참여 기간에는 대회 규정 준수와 제출 준비를 위해 저장소를 일시적으로 비공개 운영할 수 있으며, 대회 종료 후 코드와 실험 결과를 정리해 공개할 예정입니다.

## 🗓️ 14주 로드맵

| Week | 날짜 | 시간 | 주요 활동 | 결과물 |
| --- | --- | --- | --- | --- |
| **W01** | 2026.10.04 | 20:00–22:00 | OT & Lean Setup | Lean 개발 환경, 첫 번째 검증 예제 |
| **W02** | 2026.10.11 | 20:00–22:00 | Lean & Formal Mathematics | Lean·Mathlib·Autoformalization·ATP·verifier-guided agent 조사 |
| **W03** | 2026.10.18 | 20:00–22:00 | Lean Agents & Harnesses | M1 · 선행 연구 및 오픈소스 조사, 최소 실행 구조 설계 |
| **W04** | 2026.10.25 | 20:00–22:00 | Evaluation Harness | M2 · 모델 호출부터 검증·평가·결과 저장까지 연결한 harness |
| **W05** | 2026.11.01 | 20:00–22:00 | Full Benchmark Sprint | Full benchmark 결과, refactoring 전략, technical report 초안 |
| **W06** | 2026.11.08 | 20:00–22:00 | Competition Submission | M3 · 증명 결과, 실행 코드, OpenReview technical report 제출 |
| **W07** | 2026.11.15 | — | Break | 제출 기록과 문서 자유 보완 |
| **W08** | 2026.11.22 | 20:00–22:00 | Retrospective & LeanAgent Design | 성공·실패 사례 분석, 최소 LeanAgent 구조 |
| **W09** | 2026.11.29 | 20:00–22:00 | LeanAgent Prototype | 단일 생성과 반복 검증·수정 방식의 초기 비교 결과 |
| **W10** | 2026.12.06 | 20:00–22:00 | Failure-driven Refinement | 실패 유형 분석, 모델 입력과 수정 전략 개선 |
| **W11** | 2026.12.13 | 20:00–22:00 | Controlled Evaluation | M4 · 동일 benchmark·예산 기반 비교 평가 결과 |
| **W12** | 2026.12.20 | 20:00–22:00 | Generalization & Research Application | 새로운 정리와 연구 주장에 대한 검증 사례 |
| **W13** | 2026.12.27 | — | Break | 코드, 실험 결과와 문서 자유 점검 |
| **W14** | 2027.01.03 | 20:00–22:00 | Open-source Release & Final Presentation | M5 · 재현성 점검, 공개 저장소, 최종 발표와 연구 아카이빙 |

## 📚 결과물과 기록

### 🔗 결과물

- 🔗 Repository: [Pseudo-Lab/LeanAgent](https://github.com/Pseudo-Lab/LeanAgent)
- 🧪 Experiments: `TBD`
- 📝 Technical Report: `TBD`

### 📝 주요 기록

| Date | Content | Link |
| --- | --- | --- |
| 2026.10.04 | 프로젝트 킥오프 | `TBD` |
| 2026.11.08 | Lean Refactor Arena 제출 | `TBD` |
| 2027.01.03 | 최종 발표 및 오픈소스 릴리스 | `TBD` |

## 👥 함께할 분들

| 항목 | 내용 |
| --- | --- |
| 운영 기간 | 2026년 10월 4일–2027년 1월 9일 |
| 정기 모임 | 매주 일요일 20:00–22:00 |
| 장소 | 가짜연구소 Discord |
| 모집 인원 | 6명 |

### 🙋 이런 분을 기다립니다

- 수학 문제를 푸는 LLM 또는 AI agent에 관심이 있는 분
- Lean과 형식 검증을 배워보고 싶은 분
- LLM의 답을 실제로 검증하는 과정에 관심이 있는 분
- 논문 속 수학적 주장이나 증명을 더 엄밀하게 확인해보고 싶은 분
- 실패한 실험도 기록하고 팀원과 공유할 수 있는 분
- 14주 동안 담당한 코드, 실험 또는 문서 결과물을 책임감 있게 완성할 수 있는 분

### 🔥 필수 경험 및 참여 조건

- Python으로 간단한 코드를 작성하고 실행·수정할 수 있어야 합니다.
- Git/GitHub의 기본적인 사용이 가능해야 합니다.
- 프로젝트 시작 전까지 Claude Code 또는 Codex 중 하나 이상을 사용할 수 있는 환경이 필요합니다.

Lean 경험은 없어도 괜찮습니다. 함께 배우면서 시작합니다. 다만 짧은 기간 안에 대회용 실험 환경과 에이전트를 구현해야 하므로 기초 수준의 프로젝트는 아닙니다.

다음 경험이 있다면 프로젝트 진행에 도움이 됩니다.

- LLM API 또는 agent harness 사용 경험
- 수학적 증명이나 Lean·AlphaGeometry 같은 정리 증명 도구에 대한 관심
- 논문 구현, benchmark 평가 또는 오픈소스 협업 경험

프로젝트 공개 세션은 [가짜연구소 Discord](https://discord.gg/EPurkHVtp2)를 통해 참여할 수 있습니다.

## 🙏 Acknowledgement

LeanAgent 프로젝트는 가짜연구소 Open Academy로 진행됩니다. 여러분의 참여와 기여가 ‘우연한 혁명(Serendipity Revolution)’을 가능하게 합니다. 모두에게 깊은 감사를 전합니다. LeanAgent is developed as part of Pseudo-Lab's Open Research Initiative. Special thanks to our contributors and the open source community for their valuable insights and contributions.

## 😃 Contributors

<a href="https://github.com/Pseudo-Lab/LeanAgent/graphs/contributors">
  <img src="https://contrib.rocks/image?repo=Pseudo-Lab/LeanAgent" alt="LeanAgent contributors">
</a>

## 🗞️ License

이 프로젝트는 MIT License를 따릅니다.
