module Impl.External.Logging {
  import opened TypeAliases

  datatype LogLevel = Debug | Info | Warn | Error

  function {:extern "bv_logging", "l_is_logging_enabled"} is_logging_enabled(): bool

  method {:extern "", "L_LOG"} log(location: string, level: LogLevel, message: string)

  function {:extern "bv_logging", "l_fmt_uint8"} fmt_uint8(format: string, num: uint8_t): string
  function {:extern "bv_logging", "l_fmt_uint16"} fmt_uint16(format: string, num: uint16_t): string
  function {:extern "bv_logging", "l_fmt_uint32"} fmt_uint32(format: string, num: uint32_t): string
}