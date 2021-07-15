# adjust for https://github.com/coq/coq/pull/13656
s/subgoal/goal/g
# remove these lines added in https://github.com/coq/coq/pull/14596
# (for backwards compatible output)
/^Arguments/d
# same PR adds additional blank lines
/^$/d
