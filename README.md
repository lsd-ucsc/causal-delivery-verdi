# causal-delivery-verdi

## Roadmap
1. Specify DependencyTracking protocol that only tracks dependencies between messages, we *assume* that dependency precisely characterize the notion of (potential) causality.
2. Specify DependencyChecking protocol that extends DependencyChecking but only delivers a message when all its dependencies have been delivered.
3. Show VectorDependencyChecking is a special case/optimization of DependencyChecking, and CBCAST is an variant of VectorDependencyChecking.
