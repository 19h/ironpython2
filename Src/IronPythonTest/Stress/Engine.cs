// Licensed to the .NET Foundation under one or more agreements.
// The .NET Foundation licenses this file to you under the Apache 2.0 License.
// See the LICENSE file in the project root for more information.

using System;
using System.Diagnostics;
using System.Runtime.CompilerServices;
using Microsoft.Scripting.Generation;
using Microsoft.Scripting.Hosting;
using IronPython.Hosting;

using NUnit.Framework;

namespace IronPythonTest.Stress {

    [TestFixture(Category="IronPython")]
    public class Engine
#if FEATURE_REMOTING
        : MarshalByRefObject
#endif
    {
        private readonly ScriptEngine _pe;
        private readonly ScriptRuntime _env;

        public Engine() {
            // Load a script with all the utility functions that are required
            // pe.ExecuteFile(InputTestDirectory + "\\EngineTests.py");
            _env = Python.CreateRuntime();
            _pe = _env.GetEngine("py");
        }

        static long GetTotalMemory() {
            // Critical objects can take upto 3 GCs to be collected
            System.Threading.Thread.Sleep(1000);
            for (int i = 0; i < 3; i++) {
                GC.Collect();
                GC.WaitForPendingFinalizers();
            }
            return GC.GetTotalMemory(true);
        }

#if FEATURE_REFEMIT
        private void ExecuteScopes(int count) {
            for (int i = 0; i < count; i++) {
                ScriptScope scope = _pe.CreateScope();
                scope.SetVariable("x", "Hello");
                _pe.CreateScriptSourceFromFile(System.IO.Path.Combine(Common.InputTestDirectory, "simpleCommand.py")).Execute(scope);
                Assert.AreEqual(_pe.CreateScriptSourceFromString("x").Execute<int>(scope), 1);
                scope = null;
            }
        }

#if NET10_0_OR_GREATER
        [MethodImpl(MethodImplOptions.NoInlining)]
        private WeakReference[] ExecuteScopesWithMarkers(int count) {
            var markers = new WeakReference[count];
            for (int i = 0; i < count; i++) {
                ScriptScope scope = _pe.CreateScope();
                object marker = new object();
                scope.SetVariable("x", "Hello");
                scope.SetVariable("__gc_marker__", marker);
                _pe.CreateScriptSourceFromFile(System.IO.Path.Combine(Common.InputTestDirectory, "simpleCommand.py")).Execute(scope);
                Assert.AreEqual(_pe.CreateScriptSourceFromString("x").Execute<int>(scope), 1);
                markers[i] = new WeakReference(marker);
                marker = null;
                scope = null;
            }
            return markers;
        }
#endif

        [Test]
        public void ScenarioXGC() {
#if NET10_0_OR_GREATER
            // Whole-process heap size includes nondeterministic JIT, reflection,
            // adapter, and dynamic-binding caches. Marker liveness directly tests
            // whether any of the otherwise unreachable scopes are retained.
            ExecuteScopes(100);
            GetTotalMemory();
            WeakReference[] markers = ExecuteScopesWithMarkers(10000);
            GetTotalMemory();

            int retainedMarkers = 0;
            foreach (WeakReference marker in markers) {
                if (marker.IsAlive) retainedMarkers++;
            }

            System.Console.WriteLine("ScenarioGC retained {0} of {1} scope markers.", retainedMarkers, markers.Length);
            const int maxRetainedMarkers = 1;
            Assert.LessOrEqual(retainedMarkers, maxRetainedMarkers,
                "Retained scope markers must remain constant rather than scale with the cohort.");
#else
            long initialMemory = GetTotalMemory();

            ExecuteScopes(10000);

            long finalMemory = GetTotalMemory();
            long memoryUsed = finalMemory - initialMemory;
            const long memoryThreshold = 100000;

            bool emitsUncollectibleCode = Snippets.Shared.SaveSnippets || _env.Setup.DebugMode;
            if (!emitsUncollectibleCode)
            {
                System.Console.WriteLine("ScenarioGC used {0} bytes of memory.", memoryUsed);
                if (memoryUsed > memoryThreshold)
                    throw new Exception(String.Format("ScenarioGC used {0} bytes of memory. The threshold is {1} bytes", memoryUsed, memoryThreshold));
            }
            else {
                System.Console.WriteLine("Skipping memory usage test under SaveSnippets and/or Debug mode.");
            }
#endif
        }
#endif
    }
}
