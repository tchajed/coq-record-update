# adjust for https://github.com/coq/coq/pull/13656
s/subgoal/goal/g
# remove these lines added in https://github.com/coq/coq/pull/14596
# (for backwards compatible output)
/^Arguments/d
# same PR adds additional blank lines
/^$/d
# locations in Fail added in https://github.com/coq/coq/pull/15174
/^File/d
# extra space removed in https://github.com/coq/coq/pull/16130
s/= $/=/
