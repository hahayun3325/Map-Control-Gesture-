package com.example.finalhand1.DTW;

import java.util.ArrayList;
import java.util.List;

/*
    使用DTW实现的手势识别，创建记录手势数据的类
     */
public class pointHistory{
    // 关键点数据二维
    public List<Float>[]trainingHistory;// 记录历史训练数据
    public List<Float>[]recordingHistor;// 记录样本数据
    // 构造函数
    public pointHistory(){
        trainingHistory=new List[]{new ArrayList(),new ArrayList()};// 二维
        recordingHistor=new List[]{new ArrayList(),new ArrayList()};// 二维
    }
    /**
     * 获得历史训练数据
     * @return
     */
    private List<Float>[] getTrainingHistory(){
        return this.trainingHistory;
    }
    /**
     * 获得历史记录数据
     * @return
     */
    private  List<Float>[] getRecordingHistor(){
        return this.recordingHistor;
    }
}