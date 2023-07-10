/*
 * Copyright 2008 the original author or authors.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package org.powermock.modules.junit4.internal.impl;

import junit.framework.TestCase;
import junit.framework.TestSuite;
import org.junit.Before;
import org.junit.internal.runners.*;
import org.junit.runner.Description;
import org.junit.runner.Runner;
import org.junit.runner.manipulation.*;
import org.junit.runner.notification.Failure;
import org.junit.runner.notification.RunNotifier;
import org.powermock.core.classloader.annotations.MockPolicy;
import org.powermock.core.classloader.annotations.PrepareEverythingForTest;
import org.powermock.core.spi.PowerMockTestListener;
import org.powermock.modules.junit4.common.internal.PowerMockJUnitRunnerDelegate;
import org.powermock.modules.junit4.internal.impl.testcaseworkaround.PowerMockJUnit4MethodValidator;
import org.powermock.reflect.Whitebox;
import org.powermock.tests.utils.PowerMockTestNotifier;
import org.powermock.tests.utils.impl.MockPolicyInitializerImpl;
import org.powermock.tests.utils.impl.PowerMockTestNotifierImpl;
import org.powermock.tests.utils.impl.PrepareForTestExtractorImpl;
import org.powermock.tests.utils.impl.StaticConstructorSuppressExtractorImpl;

import java.lang.annotation.Annotation;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;

/**
 * A JUnit4 test runner that only runs a specified set of test methods in a test
 * class.
 * <p/>
 * <p/>
 * Many parts of this class are essentially a rip off from
 * {@link JUnit4ClassRunner} used in JUnit 4.4. It does however not extend this
 * class because we cannot let it perform the stuff it does in its constructor.
 * Another thing that different is that if an exception is thrown in the test we
 * add a tip to error message asking the user if they've not forgot to add a
 * class to test. Yet another difference is that this runner notifies the
 * PowerMock listeners of certain events.
 *
 * @see JUnit4ClassRunner
 */
@SuppressWarnings("deprecation")
public class PowerMockJUnit44RunnerDelegateImpl extends Runner implements Filterable, Sortable, PowerMockJUnitRunnerDelegate {
    private final List<Method> testMethods;
    private final TestClass testClass;
    private final PowerMockTestNotifier powerMockTestNotifier;

    public PowerMockJUnit44RunnerDelegateImpl(Class<?> klass, String[] methodsToRun, PowerMockTestListener[] listeners) throws InitializationError {
        this.powerMockTestNotifier = new PowerMockTestNotifierImpl(listeners == null ? new PowerMockTestListener[0] : listeners);
        testClass = new TestClass(klass);
        testMethods = getTestMethods(klass, methodsToRun);
        validate();
    }

    public PowerMockJUnit44RunnerDelegateImpl(Class<?> klass, String[] methodsToRun) throws InitializationError {
        this(klass, methodsToRun, null);
    }

    public PowerMockJUnit44RunnerDelegateImpl(Class<?> klass) throws InitializationError {
        this(klass, null);
    }

    @SuppressWarnings("unchecked")
    protected final List<Method> getTestMethods(Class<?> klass, String[] methodsToRun) {
        if (methodsToRun == null || methodsToRun.length == 0) {
            // The getTestMethods of TestClass is not visible so we need to look
            // it invoke it using reflection.
            try {
                return (List<Method>) Whitebox.invokeMethod(testClass, "getTestMethods");
            } catch (Throwable e) {
                throw new RuntimeException(e);
            }
        } else {
            List<Method> foundMethods = new LinkedList<Method>();
            Method[] methods = klass.getMethods();
            for (Method method : methods) {
                for (String methodName : methodsToRun) {
                    if (method.getName().equals(methodName)) {
                        foundMethods.add(method);
                    }
                }
            }
            return foundMethods;
        }
    }

    protected final void validate() throws InitializationError {
        if (!TestCase.class.isAssignableFrom(testClass.getJavaClass())) {
            MethodValidator methodValidator = new PowerMockJUnit4MethodValidator(testClass);
            methodValidator.validateMethodsForDefaultRunner();
            methodValidator.assertValid();
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void run(final RunNotifier notifier) {
        new ClassRoadie(notifier, testClass, getDescription(), new Runnable() {
            public void run() {
                runMethods(notifier);
            }
        }).runProtected();
    }

    protected void runMethods(final RunNotifier notifier) {
        final StaticConstructorSuppressExtractorImpl staticConstructorSuppressExtractorImpl = new StaticConstructorSuppressExtractorImpl();
        Class<?> testType = getTestClass();
        final ClassLoader thisClassLoader = getClass().getClassLoader();
        if (!thisClassLoader.equals(testType.getClassLoader())) {
            /*
             * The test is loaded from another classloader, this means that we
             * cannot get the correct annotations if we don't load the class
             * from the correct class loader
             */
            try {
                testType = thisClassLoader.loadClass(testType.getName());
            } catch (ClassNotFoundException e) {
                // This should never happen
                throw new RuntimeException("Internal error in PowerMock", e);
            }
        }
        for (Method method : testMethods) {
            if (staticConstructorSuppressExtractorImpl.getTestClasses(method) == null) {
                staticConstructorSuppressExtractorImpl.getTestClasses(testType);
            }
            invokeTestMethod(method, notifier);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Description getDescription() {
        Description spec = Description.createSuiteDescription(getName(), classAnnotations());
        List<Method> testMethods = this.testMethods;
        for (Method method : testMethods)
            spec.addChild(methodDescription(method));
        return spec;
    }

    protected Annotation[] classAnnotations() {
        return getTestClass().getAnnotations();
    }

    protected String getName() {
        return getTestWrappedClass().getName();
    }

    protected Object createTest() throws Exception {
        return createTestInstance();
    }

    private Object createTestInstance() throws InstantiationException, IllegalAccessException, InvocationTargetException, NoSuchMethodException {
        final TestClass testWrappedClass = getTestWrappedClass();
        Constructor<?> constructor = null;
        final Class<?> javaClass = testWrappedClass.getJavaClass();
        if (TestCase.class.isAssignableFrom(javaClass)) {
            constructor = TestSuite.getTestConstructor(javaClass.asSubclass(TestCase.class));
            if (constructor.getParameterTypes().length == 1) {
                return constructor.newInstance(javaClass.getSimpleName());
            }
        } else {
            constructor = testWrappedClass.getConstructor();
        }
        return constructor.newInstance();
    }

    protected void invokeTestMethod(final Method method, RunNotifier notifier) {
        Description description = methodDescription(method);
        final Object testInstance;
        try {
            testInstance = createTest();
        } catch (InvocationTargetException e) {
            testAborted(notifier, description, e.getTargetException());
            return;
        } catch (Exception e) {
            testAborted(notifier, description, e);
            return;
        }

        // Check if we extend from TestClass, in that case we must run the setUp
        // and tearDown methods.
        final boolean extendsFromTestCase = TestCase.class.isAssignableFrom(testClass.getJavaClass()) ? true : false;

        final TestMethod testMethod = wrapMethod(method);
        createPowerMockRunner(testInstance, testMethod, notifier, description, extendsFromTestCase).run();
    }

    protected PowerMockJUnit44MethodRunner createPowerMockRunner(final Object testInstance, final TestMethod testMethod, RunNotifier notifier,
                                                                 Description description, final boolean extendsFromTestCase) {
        return new PowerMockJUnit44MethodRunner(testInstance, testMethod, notifier, description, extendsFromTestCase);
    }

    private void testAborted(RunNotifier notifier, Description description, Throwable e) {
        notifier.fireTestStarted(description);
        notifier.fireTestFailure(new Failure(description, e));
        notifier.fireTestFinished(description);
    }

    protected TestMethod wrapMethod(Method method) {
        return new TestMethod(method, testClass);
    }

    protected String testName(Method method) {
        return method.getName();
    }

    protected Description methodDescription(Method method) {
        return Description.createTestDescription(getTestWrappedClass().getJavaClass(), testName(method), testAnnotations(method));
    }

    protected Annotation[] testAnnotations(Method method) {
        return method.getAnnotations();
    }

    public void filter(Filter filter) throws NoTestsRemainException {
        for (Iterator<Method> iter = testMethods.iterator(); iter.hasNext(); ) {
            Method method = iter.next();
            if (!filter.shouldRun(methodDescription(method)))
                iter.remove();
        }
        if (testMethods.isEmpty())
            throw new NoTestsRemainException();
    }

    public void sort(final Sorter sorter) {
        Collections.sort(testMethods, new Comparator<Method>() {
            public int compare(Method o1, Method o2) {
                return sorter.compare(methodDescription(o1), methodDescription(o2));
            }
        });
    }

    protected TestClass getTestWrappedClass() {
        return testClass;
    }

    public int getTestCount() {
        return testMethods.size();
    }

    public Class<?> getTestClass() {
        return testClass.getJavaClass();
    }

    protected class PowerMockJUnit44MethodRunner extends MethodRoadie {
        private final Object testInstance;
        private final boolean extendsFromTestCase;
        protected final TestMethod testMethod;

        protected PowerMockJUnit44MethodRunner(Object testInstance, TestMethod method, RunNotifier notifier, Description description,
                                               boolean extendsFromTestCase) {
            super(testInstance, method, notifier, description);
            this.testInstance = testInstance;
            this.extendsFromTestCase = extendsFromTestCase;
            this.testMethod = method;
        }

        @Override
        public void runBeforesThenTestThenAfters(final Runnable test) {
            executeTest(Whitebox.getInternalState(testMethod, Method.class), testInstance, test);
        }

        public void executeTest(final Method method, final Object testInstance, final Runnable test) {
            // Initialize mock policies for each test
            final ClassLoader classloader = this.getClass().getClassLoader();
            final Thread currentThread = Thread.currentThread();
            final ClassLoader originalClassLoader = currentThread.getContextClassLoader();
            currentThread.setContextClassLoader(classloader);
            new MockPolicyInitializerImpl(testClass.getJavaClass()).initialize(classloader);
            powerMockTestNotifier.notifyBeforeTestMethod(testInstance, method, new Object[0]);
            try {
                super.runBeforesThenTestThenAfters(test);
            } finally {
                currentThread.setContextClassLoader(originalClassLoader);
            }
        }

        @Override
        protected void runTestMethod() {
            try {
                try {
                    if (extendsFromTestCase) {
                        final Method setUp = Whitebox.getMethod(testInstance.getClass(), "setUp");
                        if (!setUp.isAnnotationPresent(Before.class)) {
                            Whitebox.invokeMethod(testInstance, "setUp");
                        }
                    }
                    testMethod.invoke(testInstance);
                    if ((Boolean) Whitebox.invokeMethod(testMethod, "expectsException")) {
                        addFailure(new AssertionError("Expected exception: " + getExpectedExceptionName(testMethod)));
                    }
                } catch (InvocationTargetException e) {
                    handleInvocationTargetException(testMethod, e);
                } catch (Throwable e) {
                    addFailure(e);
                } finally {
                    if (extendsFromTestCase) {
                        try {
                            Whitebox.invokeMethod(testInstance, "tearDown");
                        } catch (Throwable tearingDown) {
                            addFailure(tearingDown);
                        }
                    }
                }
            } catch (Throwable e) {
                throw new RuntimeException("Internal error in PowerMock.", e);
            }
        }

        private void handleInvocationTargetException(final TestMethod testMethod, InvocationTargetException e) throws Exception {
            Throwable actual = e.getTargetException();
            while (actual instanceof InvocationTargetException) {
                actual = ((InvocationTargetException) actual).getTargetException();
            }
            handleException(testMethod, actual);
        }

        protected void handleException(final TestMethod testMethod, Throwable actualFailure) {
            try {
                final String throwableName = actualFailure.getClass().getName();
                if (throwableName.equals("org.junit.internal.AssumptionViolatedException") || throwableName.startsWith("org.junit.Assume$AssumptionViolatedException")) {
                    return;
                } else if (!(Boolean) Whitebox.invokeMethod(testMethod, "expectsException")) {
                    final String className = actualFailure.getStackTrace()[0].getClassName();
                    final Class<?> testClassAsJavaClass = testClass.getJavaClass();
                    if (actualFailure instanceof NullPointerException
                            && !testClassAsJavaClass.getName().equals(className)
                            && !className.startsWith("java.lang")
                            && !className.startsWith("org.powermock")
                            && !className.startsWith("org.junit")
                            && !new PrepareForTestExtractorImpl().isPrepared(testClassAsJavaClass, className)
                            && !testClassAsJavaClass.isAnnotationPresent(PrepareEverythingForTest.class)
                            && !new MockPolicyInitializerImpl(testClassAsJavaClass.isAnnotationPresent(MockPolicy.class) ? testClassAsJavaClass
                            .getAnnotation(MockPolicy.class).value() : null).isPrepared(className)) {
                        Whitebox.setInternalState(actualFailure, "detailMessage", "Perhaps the class " + className + " must be prepared for test?",
                                Throwable.class);
                    }
                    addFailure(actualFailure);
                } else if ((Boolean) Whitebox.invokeMethod(testMethod, "isUnexpected", actualFailure)) {
                    String message = "Unexpected exception, expected<" + getExpectedExceptionName(testMethod) + "> but was<"
                            + actualFailure.getClass().getName() + ">";
                    addFailure(new Exception(message, actualFailure));
                }

            } catch (Exception e) {
                throw new RuntimeException("PowerMock internal error: Should never throw exception at this level", e);
            }
        }

        @SuppressWarnings("unchecked")
        private String getExpectedExceptionName(TestMethod fTestMethod) throws Exception {
            return ((Class<? extends Throwable>) Whitebox.invokeMethod(fTestMethod, "getExpectedException")).getName();
        }
    }
}
