module applications/todo_label

/*
  app: todo-label-syn
  description: a synergistic composition of the todo and label concepts

  (EOS chapter 6, "Concept Composition") 
*/

open concepts/todo
open concepts/label[Task]

sig Pending in Label {}

/* synchronized actions, or application API */

pred set_task_label [t: Task, l: Label] {
  affix[t, l]
}

pred unset_task_label [t: Task, l: Label] {
  detach[t, l]
}

pred delete_task [t: Task] {
  delete[t]
  clear[t]
}

pred add_task [t: Task] {
  add[t]
  set_task_label[t, Pending]
}

pred complete_task [t: Task] {
  complete[t]
  unset_task_label[t, Pending]
}
