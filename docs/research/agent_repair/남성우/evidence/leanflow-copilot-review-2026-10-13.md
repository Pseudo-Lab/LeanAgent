# LeanFlow와 Lean Copilot 추가 검토

2026-10-13. 원문과 구현 README 확인. 설치·유료 호출·Arena 재현 실험은 아직 수행하지 않았다.

## LeanFlow

[LeanFlow v1](https://arxiv.org/html/2607.20503v1), §4.3–4.6, §5.2/5.5, §6, Appendix B를 검토했다.

논문은 자연어 문서의 Lean 프로젝트화를 다룬다. statement 검토와 proof 수리를 분리하고, queue로 대상을 지정하며 실패 이력을 보존한다. 최종 판정은 Lean/Lake다. 두 문서 사례의 단일 실행 ablation이므로 효과의 범위가 제한된다. 구독/self-hosted 비용을 Arena의 API list-price 상한으로 그대로 환산할 수 없다.

**우리 판단:** Arena에서는 명제가 주어져 있으므로 자연어 번역과 LLM statement reviewer는 MVP에 필요하지 않다. immutable statement와 실제 문맥 보호, 문제별 지속 상태를 채택한다. helper 추가·임시 sorry가 일반적인 Arena 제출 허용이라는 해석은 하지 않는다.

### LeanProbe

[LeanProbe README](https://github.com/epfl-lara/LeanProbe): LeanInteract 기반 Python/CLI/MCP, warm 환경 재사용, declaration 검사, tactic 상태 도구. `success`는 도구 실행, `ok`는 Lean 검사 결과다. 파일을 직접 편집하지 않는다.

**우리 판단:** 자체 최적화보다 재사용 compatibility 시험을 먼저 한다. core가 결과를 정규화하고 정책·명제·공리·최종 파일 검사를 추가한다. 모든 Arena 버전에서 지원된다고 가정하지 않는다. 실패하면 CLI/direct LeanInteract adapter로 계속 진행한다.

시험: 동일 문맥 판정, 자기 원본 theorem 참조 방지, 실패 환경 격리, prefix/dependency 변경 시 cache 무효화, 진단 위치. 속도는 Strata에서 직접 측정한다. 논문의 배수를 Arena의 기대 성능으로 사용하지 않는다.

## Lean Copilot

[Lean Copilot v3](https://arxiv.org/html/2404.12534v3), §3–5를 검토했다. v1 초기 수치와 구분한다.

모델 tactic을 실제 실행해 오류·미완성·완료를 구분하고, aesop 탐색과 결합하며 premise scope를 표시한다. v3의 MIL tactic-style 168개 정리에서 search_proof 자율 해결은 63.7%(107개), aesop은 24.4%다. 이는 Arena 리팩터링 비용·점수 개선을 입증하지 않는다.

[현재 README](https://github.com/lean-dojo/LeanCopilot): 로컬/외부 모델, dependency/import·native linking 설정, 고정 Lean/Mathlib snapshot premise 검색을 설명한다.

**우리 판단:** goal→여러 tactic 후보→실행 결과의 인터페이스는 채택한다. 무변화와 미완성 변화를 구분하고, goal 수만으로 진전을 판단하지 않는다. package 자체는 후속 선택지다. 추가 환경에서 탐색한 결과는 일반 proof로 추출해 원래 환경에서 재검증한다. plugin 의존 proof를 그대로 제출하지 않는다.

로컬 추론과 API 추론의 비용을 구분한다. 목표 버전에서 premise가 존재하고 접근 가능한지도 검사한다. 설치했다고 모델 비용이 사라지는 것은 아니다. 트랙 내 혼합 모델 사용의 해석은 도입 전에 확인한다.

## 변경 결론

Python/Lean 방향 유지. LeanProbe 시험 추가, 빠른 검사와 최종 검증 분리, 지속 상태를 core에 포함, tactic 결과 세분화. 전체 LeanFlow 설치와 LeanCopilot 필수 dependency는 MVP 뒤로 미룬다.

[읽기 쉬운 전체 계획](arena-harness-plan-readable.md).
