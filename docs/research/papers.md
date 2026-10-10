# LeanAgent 관련 논문 목록

## 태그 기준

| 태그 | 분류 기준 | 자료 공유 폴더 |
| --- | --- | --- |
| `Lean&Mathlib` | Lean 환경·인터페이스, 라이브러리 구축, 선언·의존성 탐색과 활용 | Lean&Mathlib 자료 |
| `Autoformalization` | 자연어 수학 명제·증명의 Lean 변환, 대응 데이터, 의미적 일치 평가 | [autoformalization](autoformalization/README.md) |
| `Automated Theorem Proving` | 형식 명제의 증명 생성, tactic·전제 선택, 탐색, 모델 학습과 평가 | [automated-theorem-proving](automated-theorem-proving/README.md) |
| `Verifier-guided Agent` | 검증기와 상호작용하는 에이전트·도구, 피드백 기반 수정·최적화와 그 평가 | [verifier-guided-agent](verifier-guided-agent/README.md) |

## 논문 리스트

| 번호 | 논문 | 관련 태그 | 핵심 주제 / 프로젝트에서 볼 점 |
| --- | --- | --- | --- |
| 01 | [LeanDojo: Theorem Proving with Retrieval-Augmented Language Models](https://arxiv.org/abs/2306.15626v2) | `Lean&Mathlib` · `Automated Theorem Proving` · `Verifier-guided Agent` | Lean 환경 상호작용, 데이터 추출, 검색 기반 ReProver. |
| 02 | [Lean Copilot: Large Language Models as Copilots for Theorem Proving in Lean](https://arxiv.org/abs/2404.12534) | `Lean&Mathlib` · `Automated Theorem Proving` | Lean 내부 모델 실행, 증명 단계 추천, 목표 완성과 전제 선택. |
| 03 | [Process-Driven Autoformalization in Lean 4](https://arxiv.org/abs/2406.01940v2) | `Autoformalization` | 컴파일러 피드백을 활용한 과정 감독형 형식화와 평가. |
| 04 | [An Evaluation Benchmark for Autoformalization in Lean4](https://arxiv.org/abs/2406.06555) | `Autoformalization` | 자연어 수학의 Lean 형식화 능력을 평가하는 초기 벤치마크. |
| 05 | [TheoremLlama: Transforming General-Purpose LLMs into Lean4 Experts](https://arxiv.org/abs/2407.03203v2) | `Autoformalization` · `Automated Theorem Proving` | 자연어–Lean 증명 데이터, 모델 학습과 반복 증명 작성. |
| 06 | [Lean-STaR: Learning to Interleave Thinking and Proving](https://arxiv.org/abs/2407.10040v3) | `Automated Theorem Proving` | 자연어 사고와 formal tactic을 교차 생성하도록 학습. |
| 07 | [LEAN-GitHub: Compiling GitHub LEAN repositories for a versatile LEAN prover](https://arxiv.org/abs/2407.17227) | `Lean&Mathlib` · `Automated Theorem Proving` | GitHub Lean 저장소에서 학습 데이터를 추출하고 prover를 학습. |
| 08 | [Herald: A Natural Language Annotated Lean 4 Dataset](https://arxiv.org/abs/2410.10878v2) | `Lean&Mathlib` · `Autoformalization` | Mathlib 자연어 대응 데이터와 statement 번역 모델. |
| 09 | [InternLM2.5-StepProver: Advancing Automated Theorem Proving via Critic-Guided Search](https://arxiv.org/abs/2410.15700) | `Automated Theorem Proving` | critic 모델을 이용한 증명 경로 평가와 탐색. |
| 10 | [Pantograph: A Machine-to-Machine Interaction Interface for Advanced Theorem Proving, High Level Reasoning, and Data Extraction in Lean 4](https://arxiv.org/abs/2410.16429v2) | `Lean&Mathlib` · `Automated Theorem Proving` · `Verifier-guided Agent` | 증명 상태·tactic 실행 인터페이스와 탐색 알고리즘 연결. |
| 11 | [A Lean Dataset for International Math Olympiad: Small Steps towards Writing Math Proofs for Hard Problems](https://arxiv.org/abs/2411.18872) | `Automated Theorem Proving` | 어려운 IMO 증명을 보조정리 단위로 분해한 데이터와 실패 진단. |
| 12 | [LeanProgress: Guiding Search for Neural Theorem Proving via Proof Progress Prediction](https://arxiv.org/abs/2502.17925) | `Automated Theorem Proving` | 남은 증명 단계 예측으로 탐색 우선순위 결정. |
| 13 | [APOLLO: Automated LLM and Lean Collaboration for Advanced Formal Reasoning](https://arxiv.org/abs/2505.05758v2) | `Automated Theorem Proving` · `Verifier-guided Agent` | 컴파일러 피드백으로 실패한 부분 증명을 분리·수정·재검증. |
| 14 | [Lean-auto: An Interface between Lean 4 and Automated Theorem Provers](https://arxiv.org/abs/2505.14929) | `Lean&Mathlib` · `Automated Theorem Proving` | Lean 명제를 외부 자동 정리 증명기에 연결하는 변환 도구. |
| 15 | [REAL-Prover: Retrieval Augmented Lean Prover for Mathematical Reasoning](https://arxiv.org/abs/2505.20613v2) | `Automated Theorem Proving` | 검색과 단계별 증명 생성 결합, 대학 수준 수학 평가. |
| 16 | [Premise Selection for a Lean Hammer](https://arxiv.org/abs/2506.07477) | `Lean&Mathlib` · `Automated Theorem Proving` | LeanPremise·LeanHammer의 전제 선택과 자동 증명, 로컬 정리 활용. |
| 17 | [LeanExplore: A search engine for Lean 4 declarations](https://arxiv.org/abs/2506.11085) | `Lean&Mathlib` · `Automated Theorem Proving` · `Verifier-guided Agent` | 여러 패키지의 선언 검색, API·MCP를 통한 에이전트 연결. |
| 18 | [LeanGeo: Formalizing Competitional Geometry problems in Lean](https://arxiv.org/abs/2508.14644) | `Lean&Mathlib` · `Automated Theorem Proving` | 기하학 특화 라이브러리와 LeanGeo-Bench. |
| 19 | [ProofBridge: Auto-Formalization of Natural Language Proofs in Lean via Joint Embeddings](https://arxiv.org/abs/2510.15681) | `Autoformalization` · `Verifier-guided Agent` | 정리·증명 전체 번역, 공동 임베딩 검색, 반복 수정과 의미적 일치 평가. |
| 20 | [Lean Finder: Semantic Search for Mathlib That Understands User Intents](https://arxiv.org/abs/2510.15940) | `Lean&Mathlib` · `Automated Theorem Proving` | 사용자 질문·증명 상태에 맞는 Mathlib 정리 검색. |
| 21 | [Lean4Physics: Comprehensive Reasoning Framework for College-level Physics in Lean4](https://arxiv.org/abs/2510.26094) | `Lean&Mathlib` · `Automated Theorem Proving` | PhysLib과 물리 증명 벤치마크. 현재 워밍업의 PhysLib 문제에도 관련. |
| 22 | [miniF2F-Lean Revisited: Reviewing Limitations and Charting a Path Forward](https://arxiv.org/abs/2511.03108) | `Autoformalization` · `Automated Theorem Proving` | 자연어·formal statement 불일치 분석, 전체 파이프라인 평가. |
| 23 | [NL2Lean: Translating Natural Language into Lean 4 through Multi-Aspect Reinforcement Learning](https://aclanthology.org/2025.emnlp-main.1586v2.pdf) | `Autoformalization` | 의미·구조 정렬과 컴파일 보상을 활용한 Lean statement 번역 학습. |
| 24 | [Numina-Lean-Agent: An Open and General Agentic Reasoning System for Formal Mathematics](https://arxiv.org/abs/2601.14027) | `Automated Theorem Proving` · `Verifier-guided Agent` | 범용 코딩 에이전트와 Lean MCP를 결합한 시스템. |
| 25 | [Inference-Time Diversity in RL-Trained Lean Theorem Provers: A Diagnostic Study](https://arxiv.org/abs/2601.16172) | `Automated Theorem Proving` | 반복 샘플링과 tactic 구조 다양화 비교, 예산 내 후보 생성 전략. |
| 26 | [LeanArchitect: Automating Blueprint Generation for Humans and AI](https://arxiv.org/abs/2601.22554) | `Lean&Mathlib` · `Verifier-guided Agent` | Lean 선언과 blueprint를 연결하고 의존성·진행 상태를 관리하는 도구. |
| 27 | [AI4SLT: Empirical Processes in Lean 4 for Formal Statistical Learning Theory](https://arxiv.org/abs/2602.02285) | `Lean&Mathlib` · `Verifier-guided Agent` | 통계학습이론 라이브러리와 사람–AI 에이전트 협업 형식화 사례. |
| 28 | [Learning to Repair Lean Proofs from Compiler Feedback](https://arxiv.org/abs/2602.02990) | `Automated Theorem Proving` · `Verifier-guided Agent` | APRIL: 오류 증명·컴파일 진단·수정·설명 데이터와 repair 학습. |
| 29 | [VeriSoftBench: Repository-Scale Formal Verification Benchmarks for Lean](https://arxiv.org/abs/2602.18307) | `Lean&Mathlib` · `Automated Theorem Proving` · `Verifier-guided Agent` | 저장소 문맥·파일 간 의존성을 보존한 증명 평가와 문맥 제공 실험. |
| 30 | [TorchLean: Formalizing Neural Networks in Lean](https://arxiv.org/abs/2602.22631v2) | `Lean&Mathlib` | 신경망의 실행 의미, 미분, 검증을 Lean에서 다루는 프레임워크. |
| 31 | [SorryDB: Can AI Provers Complete Real-World Lean Theorems?](https://arxiv.org/abs/2603.02668) | `Automated Theorem Proving` · `Verifier-guided Agent` | 실제 형식화 프로젝트의 미완성 증명을 대상으로 prover·agent 평가. |
| 32 | [Awakening the Sleeping Agent: Lean-Specific Agentic Data Reactivates General Tool Use in Goedel Prover](https://arxiv.org/abs/2604.08388) | `Automated Theorem Proving` · `Verifier-guided Agent` | 전문 prover의 도구 호출 능력 회복과 검색 도구 사용 학습. |
| 33 | [From LLM-Generated Conjectures to Lean Formalizations: Automated Polynomial Inequality Proving via Sum-of-Squares Certificates](https://arxiv.org/abs/2605.15445) | `Autoformalization` · `Automated Theorem Proving` | LLM의 SOS 후보 생성 → 기호 계산 → Lean 인증. |
| 34 | [Lean Refactor: Multi-Objective Controllable Proof Optimization via Agentic Strategy Search](https://arxiv.org/abs/2605.20244) | `Automated Theorem Proving` · `Verifier-guided Agent` | 증명 길이·컴파일 비용·버전 호환성 최적화. 대회 목표에 직접 관련. |
| 35 | [Distilling LLM Feedback for Lean Theorem Proving](https://arxiv.org/abs/2605.30861) | `Automated Theorem Proving` | 피드백 증류 학습, 생성 다양성과 pass@k 개선. |
| 36 | [A Formally Verified Library of Mathematical Finance in Lean 4](https://arxiv.org/abs/2606.01356) | `Lean&Mathlib` | 금융수학 라이브러리, 형식화의 의미적 충실도와 사용 가정 감사. |
| 37 | [Pythagoras-Prover: Advancing Efficient Formal Proving via Augmented Lean Formalisation](https://arxiv.org/abs/2606.12594) | `Automated Theorem Proving` | 계산 효율적인 prover 학습·데이터 증강·벤치마크 평가. |
