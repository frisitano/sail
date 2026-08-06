register public_counter : word
register public_pair : pair

type test_fork = range(0, 1)

let TestBefore : int(0) = 0
let TestAfter : int(1) = 1

struct test_protocol = {
  fork : test_fork,
}

struct test_execution_profile = {
  protocol : test_protocol,
}

register public_execution_profile : test_execution_profile

function reset_counter() -> unit = public_counter = 0

function preserve_counter_snapshot(value : word) -> word = {
  if value != 0 then public_counter = value;
  let snapshot = public_counter;
  reset_counter();
  snapshot
}

function make_public_pair(value : byte) -> pair =
  struct { first = value, second = value }

function save_pair_then_read(value : byte) -> byte = {
  let next = make_public_pair(value);
  public_pair = next;
  next.second
}

function initialized_comparison_return() -> bool = {
  let snapshot = public_pair;
  let active = snapshot.first >= 1;
  active
}

val specialized_comparison : forall 'n, 0 <= 'n & 'n <= 256. int('n) -> bool
function specialized_comparison(n) = {
  let snapshot = public_pair;
  let base = n <= 4;
  let final = (n == 256) & (snapshot.first >= 1);
  base | final
}

function call_specialized_comparison() -> bool = specialized_comparison(256)

val specialized_enum_comparison : forall 'n, 0 <= 'n & 'n <= 256. int('n) -> bool
function specialized_enum_comparison(n) = {
  let execution_profile = public_execution_profile;
  let base0 = n <= 2;
  let base1 = n <= 3;
  let base2 = n <= 4;
  let final = (n == 256) & (execution_profile.protocol.fork >= TestAfter);
  base0 | base1 | base2 | final
}

function call_specialized_enum_comparison() -> bool = specialized_enum_comparison(256)

enum terminal_choice = {
  TerminalOne,
  TerminalTwo,
  TerminalThree,
  TerminalFour,
}

function terminal_enum_match(choice : terminal_choice) -> byte =
  match choice {
    TerminalOne => 1,
    TerminalTwo => 2,
    TerminalThree => 3,
    TerminalFour => 4,
  }

function terminal_enum_match_or_fatal(choice : terminal_choice) -> byte =
  match choice {
    TerminalOne => 1,
    TerminalTwo => 2,
    _ => {
      fatal_error(TestFatal);
      exit(())
    },
  }

function terminal_fixed_bytes_match(bytes : four_bytes) -> byte =
  match bytes {
    _ if eq_anything(bytes, TEST_FIXED_BYTES_ZERO) => 0,
    _ if eq_anything(bytes, TEST_FIXED_BYTES_ONE) => 1,
    _ => 2,
  }

function machine_pick_zero(index : four_index) -> byte = {
  let bytes : four_bytes = vector_init(4, 0);
  bytes[index]
}

function step(value : byte) -> word = {
  public_counter = host_mix(public_counter, value);
  public_counter
}
