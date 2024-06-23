module concepts/label[Item]

/*
  concept: label[Item]
  purpose: organize items into overlapping categories

  (EOS chapter 6, "Concept Composition") 
*/

/* state */

sig Label {}

sig LabeledItems {
  items: Item -> set Label
}

/* actions */

pred item_has_label [i: Item, l: Label] {
  l in LabeledItems.items[i]
}

pred affix [i: Item, l: Label] {
  not item_has_label[i, l]
  LabeledItems'.items[i] = LabeledItems.items[i] + l
}

pred detach [i: Item, l: Label] {
  item_has_label[i, l]
  LabeledItems'.items[i] = LabeledItems.items[i] - l
}

pred clear [i: Item] {
  LabeledItems'.items[i] = Label {}
}

fun find (l: Label): set Item {
  { i: Item | some LabeledItems.items[i] and l in LabeledItems.items[i] }
}

/* operational principles */

assert found_after_affix {
  always (all i: Item, l: Label | affix[i, l] implies i in find[l] until detach[i, l])
}

check found_after_affix

assert not_found_after_detach {
  always (all i: Item, l: Label | detach[i, l] implies i not in find[l])
}

check not_found_after_detach