module CommonTypes {
  // An optional value: either Some and contains a value, or None, and does not
  datatype Option<T> = None | Some(value: T)
}
