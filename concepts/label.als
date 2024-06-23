module concepts/label[Item]

/*
  concept: label[Item]
  purpose: organize items into overlapping categories

  (EOS chapter 6, "Concept Composition") 
*/

/* state */

sig Label {}

sig LabeledItems {
  item: Item,
  labels: set Label
}

/* actions */

pred item_has_label [i: Item, l: Label] {
  (i = LabeledItems.item) and (l in LabeledItems.*labels)
}

pred affix [i: Item, l: Label] {
  not item_has_label[i, l]
  LabeledItems'.item = LabeledItems.item
  LabeledItems'.labels = LabeledItems.labels + l
}

pred detach [i: Item, l: Label] {
  item_has_label[i, l]
  LabeledItems'.item = LabeledItems.item
  LabeledItems'.labels = LabeledItems.labels - l
}

pred clear [i: Item] {
  LabeledItems'.item = LabeledItems.item
  LabeledItems'.labels = Label {}
}

fun find (l: Label): set Item {
  { items: LabeledItems.*labels | l in items.labels }
}

/* operational principles */

// after affix(i, l) and no detach(i, l), i in find(l)

assert found_after_affix {
  always (all i : LabeledItems.*item, l: Label | affix[i, l] implies i in find[l] until detach[i, l])
}

check found_after_affix

// if no affix(i, l), or no detach(i, l), i not in find(l)
