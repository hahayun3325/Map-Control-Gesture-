/* Copyright 2019 The TensorFlow Authors. All Rights Reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
==============================================================================*/

package com.example.finalhand1.Classifer;

import static com.example.finalhand1.RecHands.myTAG;
import static java.lang.Math.min;

import android.app.Activity;
import android.graphics.RectF;
import android.os.SystemClock;
import android.os.Trace;
import android.util.Log;

import org.tensorflow.lite.DataType;
import org.tensorflow.lite.Interpreter;
import org.tensorflow.lite.nnapi.NnApiDelegate;
import org.tensorflow.lite.support.common.FileUtil;
import org.tensorflow.lite.support.common.TensorProcessor;
import org.tensorflow.lite.support.label.TensorLabel;
import org.tensorflow.lite.support.tensorbuffer.TensorBuffer;

import java.io.IOException;
import java.nio.MappedByteBuffer;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.PriorityQueue;

/**
 * A classifier specialized to label images using TensorFlow Lite.
 */
public class Classifier {
    public static final String TAG = "ClassifierWithSupport";

    /**
     * The runtime device type used for executing classification.
     */
    public enum Device {
        CPU,
        NNAPI,
        GPU
    }

    /**
     * Number of results to show in the UI.
     */
    private static final int MAX_RESULTS = 26;


    /**
     * Optional NNAPI delegate for accleration.
     */
    private NnApiDelegate nnApiDelegate = null;

    /**
     * An instance of the driver class to run model inference with Tensorflow Lite.
     */
    protected Interpreter tflite;

    /**
     * Options for configuring the Interpreter.
     */
    private final Interpreter.Options tfliteOptions = new Interpreter.Options();

    /**
     * Labels corresponding to the output of the vision model.
     */
    private final List<String> labels;

    /**
     * Output probability TensorBuffer.
     */
    private final TensorBuffer outputProbabilityBuffer;

    /**
     * Processer to apply post processing of the output probability.
     */
    private final TensorProcessor probabilityProcessor;

    /**
     * Creates a classifier with the provided configuration.
     *
     * @param activity The current Activity.
     * @param model The model to use for classification.
     * @param device The device to use for classification.
     * @param numThreads The number of threads to use for classification.
     * @return A classifier with the desired configuration.
     */

    /**
     * An immutable result returned by a Classifier describing what was recognized.
     */
    public static class Recognition {
        /**
         * A unique identifier for what has been recognized. Specific to the class, not the instance of
         * the object.
         */
        private final String id;

        /**
         * Display name for the recognition.
         */
        private final String title;

        /**
         * A sortable score for how good the recognition is relative to others. Higher should be better.
         */
        private final Float confidence;

        /**
         * Optional location within the source image for the location of the recognized object.
         */
        private RectF location;

        public Recognition(
                final String id, final String title, final Float confidence, final RectF location) {
            this.id = id;
            this.title = title;
            this.confidence = confidence;
            this.location = location;
        }

        public String getId() {
            return id;
        }

        public String getTitle() {
            return title;
        }

        public Float getConfidence() {
            return confidence;
        }

        public RectF getLocation() {
            return new RectF(location);
        }

        public void setLocation(RectF location) {
            this.location = location;
        }

        @Override
        public String toString() {
            String resultString = "";
            if (id != null) {
                resultString += "[" + id + "] ";
            }

            if (title != null) {
                resultString += title + " ";
            }

            if (confidence != null) {
                resultString += String.format("(%.1f%%) ", confidence * 100.0f);
            }

            if (location != null) {
                resultString += location + " ";
            }

            return resultString.trim();
        }
    }

    /**
     *
     * @param activity
     * @param device
     * @param numThreads
     * @throws IOException
     */
    //分类指尖动态手势 tflite
    public Classifier(Activity activity, Device device, int numThreads) throws IOException {
//    Log.v("Classifier.java","arriver");
        //加载tflite模型
        MappedByteBuffer tfliteModel = FileUtil.loadMappedFile(activity, getModelPath());
//    Log.v("Classifier.java","MappedByteBuffer");
        //手机运行类型，目前只实现CPU
        switch (device) {
            case NNAPI:
                nnApiDelegate = new NnApiDelegate();
                tfliteOptions.addDelegate(nnApiDelegate);
                break;
//      case GPU://GPU加速目前可能只有部分情况下才能使用
//        gpuDelegate = new GpuDelegate();
//        tfliteOptions.addDelegate(gpuDelegate);
//        break;
            case CPU:
                tfliteOptions.setUseXNNPACK(true);
                break;
        }
        //设置线程数量，目前只能保持一个线程 todo 存疑 只能使用一个线程是否意味着多个动态手势的识别只能存放在一个模型中呢
        tfliteOptions.setNumThreads(numThreads);
        tflite = new Interpreter(tfliteModel, tfliteOptions);
//    Log.v("Classifier.java","tflite");

        // Loads labels out from the label file.
        labels = FileUtil.loadLabels(activity, getLabelPath());

        // Reads type and shape of input and output tensors, respectively.
        int probabilityTensorIndex = 0;
        //分类模型输出shape
        int[] probabilityShape =
                tflite.getOutputTensor(probabilityTensorIndex).shape(); // {1, NUM_CLASSES}
        //模型输出数据类别
        DataType probabilityDataType = tflite.getOutputTensor(probabilityTensorIndex).dataType();

        // Creates the output tensor and its processor.
        outputProbabilityBuffer = TensorBuffer.createFixedSize(probabilityShape, probabilityDataType);

        // Creates the post processor for the output probability.
        probabilityProcessor = new TensorProcessor.Builder().build();

    }

    /**
     * Runs inference and returns the classification results.
     */
    public List<Recognition> recognizeGesture(TensorBuffer inputTensorBuffer) {
        // Logs this method so that it can be analyzed with systrace.

        // Runs the inference call.
        Trace.beginSection("runInference");
        long startTimeForReference = SystemClock.uptimeMillis();
        //运行分类模型
        tflite.run(inputTensorBuffer.getBuffer(), outputProbabilityBuffer.getBuffer().rewind());
        long endTimeForReference = SystemClock.uptimeMillis();
        Trace.endSection();
        Log.v(myTAG, "Timecost to run model inference 模型推断需要的时间: " + (endTimeForReference - startTimeForReference));

        // Gets the map of label and probability.
        Map<String, Float> labeledProbability =
                new TensorLabel(labels, probabilityProcessor.process(outputProbabilityBuffer))
                        .getMapWithFloatValue();

        // Gets top-k results.
        return getTopKProbability(labeledProbability);
    }

    //change input formate as bitmap


    /**
     * Closes the interpreter and model to release resources.
     */
    public void close() {
        if (tflite != null) {
            tflite.close();
            tflite = null;
        }
//    if (gpuDelegate != null) {
//      gpuDelegate.close();
//      gpuDelegate = null;
//    }
        if (nnApiDelegate != null) {
            nnApiDelegate.close();
            nnApiDelegate = null;
        }
    }

    /**
     *
     * @return
     */
    //获取tflite模型路径 修改
    protected String getModelPath() {
        // you can download this file from
        // see build.gradle for where to obtain this file. It should be auto
        // downloaded into assets.
//        return "point_history_classifier.tflite";
        return "point_history_classifier_model10.tflite";
    }

    /**
     *
     * @return
     */
    //获取标签文件路径 tflite 修改
    protected String getLabelPath() {
        return "point_history_classifier_label_model10.txt";
    }

    /**
     * Gets the top-k results.
     */
    private static List<Recognition> getTopKProbability(Map<String, Float> labelProb) {
        // Find the best classifications.
        PriorityQueue<Recognition> pq =
                new PriorityQueue<>(
                        MAX_RESULTS,
                        new Comparator<Recognition>() {
                            @Override
                            public int compare(Recognition lhs, Recognition rhs) {
                                // Intentionally reversed to put high confidence at the head of the queue.
                                return Float.compare(rhs.getConfidence(), lhs.getConfidence());
                            }
                        });

        for (Map.Entry<String, Float> entry : labelProb.entrySet()) {
            pq.add(new Recognition("" + entry.getKey(), entry.getKey(), entry.getValue(), null));
        }

        final ArrayList<Recognition> recognitions = new ArrayList<>();
        int recognitionsSize = min(pq.size(), MAX_RESULTS);
//        Log.d("recognitionsSize is", String.valueOf(recognitionsSize));
        for (int i = 0; i < recognitionsSize; ++i) {
            recognitions.add(pq.poll());
        }
        return recognitions;
    }
}
