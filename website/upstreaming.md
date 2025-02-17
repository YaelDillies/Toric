# Upstreaming dashboard

The eventual goal of the Toric project is to be fully upstreamed to Mathlib.

As such, it is crucial to continuously organise upstreaming from Toric to Mathlib. The way we organise this is with the following two lists, showing files with no Toric dependencies depending on whether they contain the keyword `sorry` or not.

## Files ready to upstream

The following files are `sorry`-free and do not depend on any other Toric file, meaning they can be readily PRed to Mathlib.

{% include ready_to_upstream.md %}

## Files easy to unlock

The following files do not depend on any other Toric file but still contain `sorry`, usually indicating that working on eliminating those sorries might unblock some part of the project.

{% include easy_to_unlock.md %}
