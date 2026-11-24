defmodule ReductionBounds.VerificationJobsTest do
  use ExUnit.Case, async: false
  alias ReductionBounds.{ProofPreparation, VerificationJobs}

  setup do
    server = start_supervised!({VerificationJobs, name: nil, limit: 2})
    %{server: server}
  end

  test "bounds independent callers and restores slots after exceptions", %{server: server} do
    parent = self()

    tasks =
      for n <- 1..4 do
        spawn_owned(fn ->
          VerificationJobs.run(
            fn ->
              send(parent, {:running, n, self()})

              receive do
                :continue -> :ok
              end
            end,
            server
          )

          send(parent, {:finished, n})
        end)
      end

    on_exit(fn -> Enum.each(tasks, &Process.exit(&1, :kill)) end)
    assert_receive {:running, _, first}
    assert_receive {:running, _, second}
    await(fn -> VerificationJobs.stats(server).queued == 2 end)
    assert %{active: 2, peak: 2} = VerificationJobs.stats(server)
    send(first, :continue)
    assert_receive {:running, _, third}
    send(second, :continue)
    assert_receive {:running, _, fourth}
    send(third, :continue)
    send(fourth, :continue)
    for _ <- 1..4, do: assert_receive({:finished, _})
    assert %{active: 0, queued: 0, peak: 2} = VerificationJobs.stats(server)

    assert_raise RuntimeError, "failed job", fn ->
      VerificationJobs.run(fn -> raise "failed job" end, server)
    end

    assert {:retried, %{limit: 2}} = VerificationJobs.run(fn -> :retried end, server)
    assert VerificationJobs.stats(server).active == 0
  end

  test "owner death releases a slot and cancelled waiters never run" do
    server = start_supervised!({VerificationJobs, name: nil, limit: 1}, id: :single)
    parent = self()

    owner =
      spawn_owned(fn ->
        VerificationJobs.run(
          fn ->
            send(parent, {:owner_started, self()})

            receive do
              :never -> :ok
            end
          end,
          server
        )
      end)

    assert_receive {:owner_started, worker}
    worker_monitor = Process.monitor(worker)

    cancelled =
      spawn_owned(fn -> VerificationJobs.run(fn -> send(parent, :cancelled_ran) end, server) end)

    await(fn -> VerificationJobs.stats(server).queued == 1 end)

    survivor =
      spawn_owned(fn -> VerificationJobs.run(fn -> send(parent, :survivor_ran) end, server) end)

    await(fn -> VerificationJobs.stats(server).queued == 2 end)
    Process.exit(cancelled, :kill)
    await(fn -> VerificationJobs.stats(server).queued == 1 end)
    Process.exit(owner, :kill)
    assert_receive {:DOWN, ^worker_monitor, :process, ^worker, _}
    assert_receive :survivor_ran
    await(fn -> VerificationJobs.stats(server).active == 0 end)
    refute_received :cancelled_ran
    await(fn -> not Process.alive?(survivor) end)
  end

  test "shared preparation waiters do not occupy job slots" do
    server = start_supervised!({VerificationJobs, name: nil, limit: 1}, id: :single)
    parent = self()

    blocker =
      spawn_owned(fn ->
        VerificationJobs.run(
          fn ->
            send(parent, {:blocked, self()})

            receive do
              :continue -> :ok
            end
          end,
          server
        )
      end)

    assert_receive {:blocked, blocked_worker}
    keys = %{"theory" => make_ref()}

    run = fn ->
      ProofPreparation.coordinate(keys, fn ->
        {reports, _} = VerificationJobs.run(fn -> [%{module: "theory", status: :ok}] end, server)
        reports
      end)

      send(parent, :prepared)
    end

    owner = spawn_owned(run)
    await(fn -> VerificationJobs.stats(server).queued == 1 end)
    waiter = spawn_owned(run)

    await(fn ->
      Enum.any?(:sys.get_state(ProofPreparation).waiters, fn {from, _, _} ->
        elem(from, 0) == waiter
      end)
    end)

    assert VerificationJobs.stats(server).queued == 1
    send(blocked_worker, :continue)
    assert_receive :prepared
    assert_receive :prepared
    await(fn -> VerificationJobs.stats(server).active == 0 end)
    on_exit(fn -> Enum.each([blocker, owner, waiter], &Process.exit(&1, :kill)) end)
  end

  test "public target deadlines include queueing and keep target association" do
    parent = self()
    limit = VerificationJobs.stats().limit

    blockers =
      for _ <- 1..limit do
        spawn_owned(fn ->
          VerificationJobs.run(fn ->
            send(parent, {:held, self()})

            receive do
              :continue -> :ok
            end
          end)
        end)
      end

    on_exit(fn -> Enum.each(blockers, &Process.exit(&1, :kill)) end)

    held =
      for _ <- 1..limit do
        assert_receive {:held, worker}
        worker
      end

    [{module, beam}] =
      Code.compile_string(
        "defmodule ReductionBounds.JobBudgetFixture do\n @compile :debug_info\n def first, do: 1\n def second, do: 2\nend"
      )

    on_exit(fn ->
      :code.purge(module)
      :code.delete(module)
    end)

    targets = [{module, :first, 0}, {module, :second, 0}]

    proof = %Lynx.Lean{
      source: "theorem queueProbe : True := by trivial",
      file: "queue_probe.lean",
      span: {1, 1},
      indentation: 0
    }

    task =
      Task.async(fn ->
        ReductionBounds.verify(targets, postlude: proof, beam_binaries: [beam], timeout: 1_000)
      end)

    await(fn ->
      case Task.yield(task, 0) do
        {:ok, result} -> flunk("request finished before queue admission: #{inspect(result)}")
        _ -> VerificationJobs.stats().queued == 2
      end
    end)

    assert {:ok, results} = Task.await(task, 5_000)
    assert results == Enum.map(targets, &{&1, {:error, :timeout}})
    await(fn -> VerificationJobs.stats().queued == 0 end)
    assert VerificationJobs.stats().active == limit
    Enum.each(held, &send(&1, :continue))
    await(fn -> VerificationJobs.stats().active == 0 end)
  end

  test "restarting the budget terminates old workers before admitting new ones" do
    parent = self()
    server = Process.whereis(VerificationJobs)
    supervisor = Process.whereis(ReductionBounds.VerificationWorkers)

    owner =
      spawn_owned(fn ->
        VerificationJobs.run(fn ->
          send(parent, {:worker, self()})

          receive do
            :never -> :ok
          end
        end)
      end)

    assert_receive {:worker, worker}
    monitor = Process.monitor(worker)
    Process.exit(server, :kill)
    assert_receive {:DOWN, ^monitor, :process, ^worker, _}, 1_000

    await(fn ->
      pid = Process.whereis(VerificationJobs)
      workers = Process.whereis(ReductionBounds.VerificationWorkers)
      is_pid(pid) and pid != server and is_pid(workers) and workers != supervisor
    end)

    await(fn -> not Process.alive?(owner) end)
    assert VerificationJobs.stats().active == 0
    assert {:recovered, _} = VerificationJobs.run(fn -> :recovered end)
  end

  test "rejects invalid job limits" do
    for value <- [0, -1, :infinity] do
      assert_raise ArgumentError, fn -> VerificationJobs.start_link(limit: value, name: nil) end
    end
  end

  defp spawn_owned(fun) do
    pid = spawn(fun)
    on_exit(fn -> Process.exit(pid, :kill) end)
    pid
  end

  defp await(fun, attempts \\ 400) do
    cond do
      fun.() ->
        :ok

      attempts == 0 ->
        flunk("condition did not become true")

      true ->
        Process.sleep(5)
        await(fun, attempts - 1)
    end
  end
end
