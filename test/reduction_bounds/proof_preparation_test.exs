defmodule ReductionBounds.ProofPreparationTest do
  use ExUnit.Case, async: false
  alias ReductionBounds.ProofPreparation

  test "overlapping cold dependencies wait while independent closures can proceed" do
    context = make_ref()
    keys = %{"shared" => {context, :shared}}
    parent = self()

    owner =
      spawn(fn ->
        ProofPreparation.coordinate(keys, fn ->
          send(parent, {:started, self()})

          receive do
            :continue -> :ok
          end

          [%{module: "shared", status: :ok}]
        end)

        send(parent, :owner_finished)
      end)

    on_exit(fn -> Process.exit(owner, :kill) end)
    assert_receive {:started, ^owner}

    waiter =
      spawn(fn ->
        ProofPreparation.coordinate(keys, fn ->
          send(parent, :waiter_started)
          [%{module: "shared", status: :ok}]
        end)

        send(parent, :waiter_finished)
      end)

    on_exit(fn -> Process.exit(waiter, :kill) end)
    refute_receive :waiter_started, 30

    assert [%{status: :ok}] =
             ProofPreparation.coordinate(%{"independent" => {context, :other}}, fn ->
               [%{module: "independent", status: :ok}]
             end)

    send(owner, :continue)
    assert_receive :owner_finished
    assert_receive :waiter_started
    assert_receive :waiter_finished
  end

  test "failed and raised preparation is released so later callers can retry" do
    context = make_ref()
    keys = %{"shared" => {context, :shared}}

    assert_raise RuntimeError, "preparation failed", fn ->
      ProofPreparation.coordinate(keys, fn -> raise "preparation failed" end)
    end

    assert [%{status: :error}] =
             ProofPreparation.coordinate(keys, fn -> [%{module: "shared", status: :error}] end)

    assert [%{status: :ok}] =
             ProofPreparation.coordinate(keys, fn -> [%{module: "shared", status: :ok}] end)

    state = :sys.get_state(ProofPreparation)
    assert MapSet.member?(state.ready, keys["shared"])
    assert state.held[keys["shared"]] == nil
  end

  test "owner death releases its closure and a cancelled waiter never starts work" do
    context = make_ref()
    keys = %{"shared" => {context, :shared}}
    parent = self()

    owner =
      spawn(fn ->
        ProofPreparation.coordinate(keys, fn ->
          send(parent, {:owner_ready, self()})

          receive do
            :never -> []
          end
        end)
      end)

    assert_receive {:owner_ready, ^owner}

    cancelled =
      spawn(fn ->
        ProofPreparation.coordinate(keys, fn ->
          send(parent, :cancelled_work_started)
          [%{module: "shared", status: :ok}]
        end)
      end)

    await_waiter(cancelled)
    monitor = Process.monitor(cancelled)
    Process.exit(cancelled, :kill)
    assert_receive {:DOWN, ^monitor, :process, ^cancelled, :killed}
    owner_monitor = Process.monitor(owner)
    Process.exit(owner, :kill)
    assert_receive {:DOWN, ^owner_monitor, :process, ^owner, :killed}

    assert [%{status: :ok}] =
             ProofPreparation.coordinate(keys, fn -> [%{module: "shared", status: :ok}] end)

    refute_receive :cancelled_work_started, 30
  end

  defp await_waiter(pid, attempts \\ 200) do
    queued =
      Enum.any?(:sys.get_state(ProofPreparation).waiters, fn {from, _, _} ->
        elem(from, 0) == pid
      end)

    cond do
      queued ->
        :ok

      attempts == 0 ->
        flunk("caller did not enter the preparation queue")

      true ->
        Process.sleep(5)
        await_waiter(pid, attempts - 1)
    end
  end

  test "a previously ready dependency is evicted after a failed or interrupted retry" do
    keys = %{"shared" => {make_ref(), :shared}}
    ProofPreparation.coordinate(keys, fn -> [%{module: "shared", status: :ok}] end)
    ProofPreparation.coordinate(keys, fn -> [%{module: "shared", status: :error}] end)
    refute MapSet.member?(:sys.get_state(ProofPreparation).ready, keys["shared"])
    ProofPreparation.coordinate(keys, fn -> [%{module: "shared", status: :ok}] end)

    assert_raise RuntimeError, fn ->
      ProofPreparation.coordinate(keys, fn -> raise "retry failed" end)
    end

    refute MapSet.member?(:sys.get_state(ProofPreparation).ready, keys["shared"])
  end

  test "readiness is scoped to each finalized dependency identity" do
    context = make_ref()
    first = %{"shared" => {context, :first}}
    second = %{"shared" => {context, :second}}
    ProofPreparation.coordinate(first, fn -> [%{module: "shared", status: :ok}] end)
    ProofPreparation.coordinate(second, fn -> [%{module: "shared", status: :error}] end)
    state = :sys.get_state(ProofPreparation)
    assert MapSet.member?(state.ready, first["shared"])
    refute MapSet.member?(state.ready, second["shared"])
  end
end
