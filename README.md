# causal-delivery-verdi

## Roadmap
1. Specify CausalTracking protocol that only tracks causalities/dependencies between messages.
2. Specify CausalDelivery protocol that extends CausalTracking but only delivers a message when all its dependencies have been delivered.
3. Show CBCAST is a special case/optimization of CausalDelivery.
