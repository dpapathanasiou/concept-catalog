module concepts/todo

/*
  concept: todo
  purpose: keep track of tasks

  (EOS chapter 6, "Concept Composition") 
*/

/* state */

var sig Task {}

var sig Done in Task {}
var sig Pending in Task {}

/* actions */

pred add [t : Task] {
  not (t in Done) and not (t in Pending)
  Pending = Pending + t
}

pred delete [t : Task] {
  t in Done
  Done = Done - t
  t in Pending
  Pending = Pending - t
}

pred complete [t : Task] {
  t in Pending
  Done = Done + t
  Pending = Pending - t
}

/* operational principles */

assert pending_after_add {
  always (all t : Task | add[t] implies t in Pending until complete[t] or delete[t])
}

check pending_after_add

assert done_after_complete {
  always (all t : Task | complete[t] implies t in Done until delete[t])
}

check done_after_complete