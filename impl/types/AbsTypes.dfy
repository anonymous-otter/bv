module Impl.AbsTypes {
  datatype ExternalHandle<T> = ExternalHandle(obj: T)

  function {:extern "extern_types", "new_external_handle"} {:axiom} NewExternalHandle<T>(obj: T): ExternalHandle<T>
    ensures NewExternalHandle(obj).obj == obj

  datatype DataPossibleView<T> = Unavailable | View(view: T)
}