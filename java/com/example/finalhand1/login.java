package com.example.finalhand1;

import static com.example.finalhand1.RecHands.image_width;
import static com.example.finalhand1.RecHands.myTAG;

import static java.lang.Boolean.FALSE;
import static java.lang.Boolean.TRUE;
import static java.lang.Math.max;
import static java.lang.Math.min;

import android.Manifest;
import android.content.Context;
import android.content.Intent;
import android.content.SharedPreferences;
import android.graphics.SurfaceTexture;
import android.media.AudioManager;
import android.os.Build;
import android.os.Bundle;
import android.os.Environment;
import android.provider.Settings;
import android.util.Log;
import android.util.Size;
import android.view.KeyEvent;
import android.view.SurfaceHolder;
import android.view.SurfaceView;
import android.view.View;
import android.view.ViewGroup;
import android.view.inputmethod.EditorInfo;
import android.widget.AdapterView;
import android.widget.Button;
import android.widget.CompoundButton;
import android.widget.EditText;
import android.widget.ListView;
import android.widget.ProgressBar;
import android.widget.Switch;
import android.widget.TextView;
import android.widget.Toast;

import androidx.annotation.Nullable;
import androidx.appcompat.app.AppCompatActivity;
import androidx.constraintlayout.widget.ConstraintLayout;
import androidx.core.app.ActivityCompat;
import androidx.preference.PreferenceManager;

import com.example.finalhand1.DTW.pointHistory;
import com.example.finalhand1.mainmenuUI.MainMenu;
import com.example.finalhand1.mainmenuUI.MenuAdapter;
import com.google.mediapipe.components.CameraHelper;
import com.google.mediapipe.components.CameraXPreviewHelper;
import com.google.mediapipe.components.ExternalTextureConverter;
import com.google.mediapipe.components.FrameProcessor;
import com.google.mediapipe.components.PermissionHelper;
import com.google.mediapipe.formats.proto.LandmarkProto;
import com.google.mediapipe.framework.AndroidAssetUtil;
import com.google.mediapipe.framework.AndroidPacketCreator;
import com.google.mediapipe.framework.Packet;
import com.google.mediapipe.framework.PacketGetter;
import com.google.mediapipe.glutil.EglManager;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public class login extends AppCompatActivity implements View.OnClickListener{
    /*
    成员变量
     */
    private TextView stateText;// 当前状态展示的文本框
    private TextView userName;// 获得用户姓名的文本框
    private EditText userNameEnter;// 获得用户姓名的文本框
    private Switch stateSwitch;// 选择
    private List<MainMenu> fruitList = new ArrayList<>();// 菜单list
    private BrightnessAdapter myAPP_BrightnessAdapter;// 屏幕亮度自适应调节
    private SurfaceView previewDisplayView;// 视频图像展示的界面设置
    private FrameProcessor processor;// 展示时的进程
    private CameraXPreviewHelper cameraHelper;// 视频图像的设置器
    private ExternalTextureConverter converter;// 外部纹理转换器
    private SurfaceTexture previewFrameTexture;// 界面的纹理
    private EglManager eglManager;// 安卓图形图像处理的接口
    private Button userNameRecord;// 记录用户姓名的按钮
    /*
    mediapipie相关参数的设置
     */
    private static final String BINARY_GRAPH_NAME = "hand_tracking_mobile_gpu.binarypb";
    private static final String INPUT_VIDEO_STREAM_NAME = "input_video";
    private static final String OUTPUT_VIDEO_STREAM_NAME = "output_video";
    private static final String OUTPUT_HAND_PRESENCE_STREAM_NAME = "hand_presence";
    private static final String OUTPUT_LANDMARKS_STREAM_NAME = "hand_landmarks";
    private static final String INPUT_NUM_HANDS_SIDE_PACKET_NAME = "num_hands";
    private static final int NUM_HANDS = 1;
    // 因为OpenGL表示图像时假设图像原点在左下角，而MediaPipe通常假设图像原点在左上角，所以要翻转
    private static final boolean FLIP_FRAMES_VERTICALLY = true;
    HashMap string_to_num_map = new HashMap();// 存放需要做出响应的手势的label
    //手势识别的进度条
    ProgressBar progressBar;
    /*
    手势响应时候需要的计数
     */
    int flag_activity = 0;
    private int array_to_count_activity[] = new int[20];
    private int next_song = 0;
    // 是否开始进行手势序列记录的标志 默认是false
    private boolean record_flag=false;
    // 记录手势序列的列表
    public List<pointHistory> temp21keypoints;// 记录手掌21个关键点的情况
    public pointHistory temp_HandRecord4;// 记录关键点4的轨迹
    public pointHistory temp_HandRecord8;// 记录关键点8的轨迹
    // 所使用的摄像头
    private static final boolean USE_FRONT_CAMERA = true;
    // 设定文件存放的路径
    private static final String path=Environment.getExternalStorageDirectory().toString()+"/CsvTest";
    // 设定写入文件的名字
    private static final String fileName="aa.csv";
    // 获得文本框中写入的用户的姓名
    private String temp_userName="administrator";// 默认状态下的用户姓名
    // 判断当前进行手势识别操作还是进行手势序列的收集
    // 是否连接视频流
    private boolean vedio_flag=false;
    // 记录输入次数
    private int userName_EnterTimes=0;
    // 记录当前采集的手势名称
    private String record_gesture=null;
    // 显示当前状态的字符串
    private String textShow=null;
    // 选择的关键点的数量
    private int n_keypoints=21;


    @Override
    protected void onCreate(@Nullable Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        setContentView(R.layout.login_layout);
        // 记录手势序列的对象的初始化
        temp_HandRecord4=new pointHistory();
        temp_HandRecord8=new pointHistory();
        temp21keypoints=new ArrayList<>();
        // 向列表中添加21个关键点的对象
        for(int i=0;i<n_keypoints;i++){
            temp21keypoints.add(new pointHistory());
        }
        /*
        基本控件的获得
         */
        stateSwitch=findViewById(R.id.stateSwith);
        stateText=findViewById(R.id.stateResemble);
//        userName=findViewById(R.id.userName);
//        userNameEnter=findViewById(R.id.userNameEnter);
//        userNameRecord=findViewById(R.id.userNameRecord);
        /** 输入法动作发送, 设置Ime选项(编辑信息.发送指令) */
//        userNameEnter.setImeOptions(EditorInfo.IME_ACTION_DONE);
        /*
        https://blog.csdn.net/kongbaidepao/article/details/64132147
         */
        // : 10/8/2022 当前点按两次回车案件有响应 但是软键盘退出再次响应，并且出现闪退 SurfaceTexture is already attached to a context 最后使用的是按钮解决
//        userNameEnter.setOnEditorActionListener(new EditText.OnEditorActionListener() {
//           @Override
//           public boolean onEditorAction(TextView v, int actionId, KeyEvent event) {
//               Log.d(myTAG, ""+actionId);
//
//
//               // EditorInfo.IME_ACTION_GO          android:imeOptions="actionGo"
//               // EditorInfo.IME_ACTION_SEARCH      android:imeOptions="actionSearch"
//               // EditorInfo.IME_ACTION_SEND        android:imeOptions="actionSend"
//               // EditorInfo.IME_ACTION_NEXT        android:imeOptions="actionNext"
//               // EditorInfo.IME_ACTION_UNSPECIFIED  android:imeOptions="actionUnspecified"
////               if (actionId == EditorInfo.IME_ACTION_SEND
////                       || actionId == EditorInfo.IME_ACTION_DONE
////                       || (event != null) && KeyEvent.KEYCODE_ENTER
////                       == event.getKeyCode() && KeyEvent.ACTION_DOWN == event.getAction()) {
//               if ((event != null) && KeyEvent.KEYCODE_ENTER
//                       == event.getKeyCode() && KeyEvent.ACTION_DOWN == event.getAction()) {
//                   /*
//                   点按软键盘回车后的操作
//                    */
//                   if(v.getText().toString().isEmpty()){
//                       // 当输入内容为空
//                       stateText.setText("当前没有输入用户名");
//                   }else {
//                       temp_userName=v.getText().toString();
//                       String temp_state=String.format("当前输入的用户名：%s",temp_userName);
//                       stateText.setText(temp_state);
//                    /*
//                    重点 由于mediapipe在展示视频流时将SurfaceTexture占用，所以先完成用户填写后再连接视频
//                     */
//                       Log.d(myTAG, "键盘回车按钮的响应");
//                       vedio_flag=true;
//                       // 清除焦点
//                       // 引入视频流
//                       if (userName_EnterTimes==0){
////                           userNameEnter.clearFocus();
//                           startCamera();
//                       }
//                       userName_EnterTimes+=1;
//                   }
//                   return true;
//               }
//               return true;
//           }});
        // 设置按钮的点按响应
//        userNameRecord.setOnClickListener(new View.OnClickListener() {
//            @Override
//            public void onClick(View view) {
//                if(userNameEnter.getText().toString().isEmpty()){
//                    // 当输入内容为空
//                    stateText.setText("当前没有输入用户名");
//                }else {
//                    temp_userName=userNameEnter.getText().toString();
//                    String temp_state=String.format("当前输入的用户名：%s",temp_userName);
//                    stateText.setText(temp_state);
//                    /*
//                    重点 由于mediapipe在展示视频流时将SurfaceTexture占用，所以先完成用户填写后再连接视频
//                     */
//                    Log.d(myTAG, "键盘回车按钮的响应");
//                    vedio_flag=true;// 设置在onResum中的摄像头开启函数可以工作
//                    // 清除焦点
//                    // 引入视频流
//                    if (userName_EnterTimes==0){
////                           userNameEnter.clearFocus();
//                        startCamera();
//                    }
//                    userName_EnterTimes+=1;
//                }
//            }
//        });
//        userNameEnter.setOnEditorActionListener(new TextView.OnEditorActionListener() {
//            @Override
//            public boolean onEditorAction(TextView textView, int i, KeyEvent keyEvent) {
//                if(textView.getText().toString().isEmpty()){
//                    // 当输入内容为空
//                    stateText.setText("当前没有输入用户名");
//                }else {
//                    temp_userName=textView.getText().toString();
//                    String temp_state=String.format("当前输入的用户名：%s",temp_userName);
//                    stateText.setText(temp_state);
//                    /*
//                    重点 由于mediapipe在展示视频流时将SurfaceTexture占用，所以先完成用户填写后再连接视频
//                     */
//                    vedio_flag=true;
//                    // 清除焦点
//                    userNameEnter.clearFocus();
//                    // 引入视频流
//                    startCamera();
//                }
//                return false;
//            }
//        });
        startCamera();
        progressBar = (ProgressBar) findViewById(R.id.progress_bar_login);// 手势识别进度显示
        stateSwitch.setOnCheckedChangeListener(new CompoundButton.OnCheckedChangeListener() {
            // 对开关响应的部分
            @Override
            public void onCheckedChanged(CompoundButton compoundButton, boolean b) {
                if(b){
                    // 当开关打开时，开始记录手势序列
                    record_flag=true;
                    // 状态更新
                    textShow=String.format("当前进行手势采集%s，动作完成后关闭开关",record_gesture);
                    stateText.setText(textShow);
                    // 对原有的关键点序列的list进行清空
                    clearKeyPointHistory();
                }else if(!b){
                    // 当开关关闭，将数据记录在文件中
                    record_flag=false;
                    // 获得用户名
                    // TODO: 10/6/2022 获得用户名的edittext存在问题
//                    if(userNameEnter.getText().toString()=="USERNAME:请填写用户姓名"){
//                        // 判定为用户没有输入过用户名
//                        temp_userName="administrator";
//                    }else{
//                        temp_userName=userNameEnter.getText().toString();
//                        Log.d(myTAG, "当前填入的文本框中的内容:"+temp_userName);
//                    }
//                    temp_userName="administrator";
                    // 状态更新
                    textShow=String.format("手势%s记录完成，已经保存在%s//%s文件中",record_gesture,path,fileName);
                    stateText.setText(textShow);
                    askForPermission();// 获得写文件需要的权限
                    writeRecord();// 将记录的序列写在csv文件中
                }
            }
        });
        //对于主界面中的列表进行初始化
        initFruits();//对列表中存在的MainMenu进行初始化
        MenuAdapter adapter = new MenuAdapter(this, R.layout.main_menu_ui_item, fruitList);//其中fruitList列表中的所有元素都是MainMenu
        ListView listView = (ListView) findViewById(R.id.list_view_login);// 获得前端界面中的list
        listView.setAdapter(adapter);
        // 对于listview中点击事件添加
        listView.setOnItemClickListener(new AdapterView.OnItemClickListener() {
            //onItemClick通过 position参数判断出用户点击的是哪一个子项
            @Override
            public void onItemClick(AdapterView<?> parent, View view, int position, long id) {
                switch (position) {
                    case 0://注意 listview中每一个列表单元从0开始数数
                        doAction(0);// 退出当前界面
                        break;
                    case 1://注意 listview中每一个列表单元从0开始数数
                        doAction(1);// 退出当前界面
                        break;
                    case 2://注意 listview中每一个列表单元从0开始数数
                        doAction(2);// 退出当前界面
                        break;
                    case 3://注意 listview中每一个列表单元从0开始数数
                        doAction(3);// 退出当前界面
                        break;
                    case 4://注意 listview中每一个列表单元从0开始数数
                        doAction(4);// 退出当前界面
                        break;
                    case 5://注意 listview中每一个列表单元从0开始数数
                        doAction(5);// 退出当前界面
                        break;
                }
            }
        });
        // 设置光线传感器进行屏幕亮度自适应调节
        myAPP_BrightnessAdapter =new BrightnessAdapter(getApplicationContext(),getWindow());
        myAPP_BrightnessAdapter.regist();
        // 视频图像展示界面的设置
        previewDisplayView = new SurfaceView(this);
        setupPreviewDisplayView();
        // 动态权限的获取
        PermissionHelper.checkAndRequestCameraPermissions(this);
        // 文件的读写需要的权限的申请
        ActivityCompat.requestPermissions(this, new String[]{Manifest.permission.WRITE_EXTERNAL_STORAGE}, 222);
        // 初始化assets管理器，以便MediaPipe应用资源
        AndroidAssetUtil.initializeNativeAssetManager(this);
        eglManager = new EglManager(null);
        // 通过加载获取一个帧进程——以及相关参数的设置
        processor = new FrameProcessor(
                this,
                eglManager.getNativeContext(),
                BINARY_GRAPH_NAME,
                INPUT_VIDEO_STREAM_NAME,
                OUTPUT_VIDEO_STREAM_NAME);
        processor.getVideoSurfaceOutput().setFlipY(FLIP_FRAMES_VERTICALLY);
        // 安卓数据包的创建
        AndroidPacketCreator packetCreator = processor.getPacketCreator();
        Map<String, Packet> inputSidePackets = new HashMap<>();
        inputSidePackets.put(INPUT_NUM_HANDS_SIDE_PACKET_NAME, packetCreator.createInt32(NUM_HANDS));// 设置数据包中需要捕获的手掌的数量
        processor.setInputSidePackets(inputSidePackets);

        // 设置手势处理进程中对于手势数据包处理的响应
        processor.addPacketCallback(
                OUTPUT_LANDMARKS_STREAM_NAME,
                (packet) -> {
                    List<LandmarkProto.NormalizedLandmarkList> multiHandLandmarks =
                            PacketGetter.getProtoVector(packet, LandmarkProto.NormalizedLandmarkList.parser());
                    if(isHandInRecZone(multiHandLandmarks)){
                        // 当手掌在识别区域内，才对手势进行响应
                        HandleTheHands(multiHandLandmarks);
                    }
                }
        );
    }
    /**
     * 对关键点序列进行清空的操作
     */
    private void clearKeyPointHistory(){
        temp_HandRecord4.trainingHistory[0].clear();
        temp_HandRecord4.trainingHistory[1].clear();
        temp_HandRecord8.trainingHistory[0].clear();
        temp_HandRecord8.trainingHistory[1].clear();
        for(int i=0;i<n_keypoints;i++){
            temp21keypoints.get(i).trainingHistory[0].clear();
            temp21keypoints.get(i).trainingHistory[1].clear();
        }
    }
    /**
     * 界面list菜单的初始化
     */
    private void initFruits() {
        fruitList.clear();
        // 设置列表单元格的文字和图片
        MainMenu userOne=new MainMenu("一",R.drawable.one);
        fruitList.add(userOne);
        MainMenu userTwo=new MainMenu("二",R.drawable.two);
        fruitList.add(userTwo);
        MainMenu userPrev=new MainMenu("上一首",R.drawable.previous_song);
        fruitList.add(userPrev);
        MainMenu userNext=new MainMenu("下一首",R.drawable.next_song);
        fruitList.add(userNext);
        MainMenu userPause=new MainMenu("暂停",R.drawable.puase_song);
        fruitList.add(userPause);
        MainMenu finish_app = new MainMenu("退出", R.drawable.finish_sign);
        fruitList.add(finish_app);
    }

    /**
     * 对操作手势做出的响应
     * @param title 静态手势label
     */
    private void doAction(Integer title) {
        Runtime runtime = Runtime.getRuntime();
        if(title==0){
            record_gesture="one";
        }else if(title==1){
            record_gesture="two";
        }else if(title==2){
            record_gesture="prev_song";
        }else if(title==3){
            record_gesture="next_song";
        }else if(title==4){
            record_gesture="pause";
        }
        else if (title == 5) {
            // 退出界面的操作
            finish();
        }
        try {
            Thread.sleep(500);
        } catch (Exception e) {
            e.printStackTrace();
        }
        textShow=String.format("选择手势：%s",record_gesture);
        stateText.setText(textShow);
    }

    /**
     * 视频图像展示界面的设置（对不同视频展示情况设置响应）
     */
    private void setupPreviewDisplayView() {
        previewDisplayView.setVisibility(View.GONE);
        ViewGroup viewGroup = findViewById(R.id.preview_display_layout_login);
        viewGroup.addView(previewDisplayView);

        previewDisplayView
                .getHolder()
                .addCallback(
                        new SurfaceHolder.Callback() {
                            @Override
                            public void surfaceCreated(SurfaceHolder holder) {
                                processor.getVideoSurfaceOutput().setSurface(holder.getSurface());
                            }

                            @Override
                            public void surfaceChanged(SurfaceHolder holder, int format, int width, int height) {
                                onPreviewDisplaySurfaceChanged(holder, format, width, height);
                            }

                            @Override
                            public void surfaceDestroyed(SurfaceHolder holder) {
                                processor.getVideoSurfaceOutput().setSurface(null);
                            }
                        });
    }

    /**
     * 当视频展示界面发生变化，自适应调节视频图像的函数
     * @param holder
     * @param format
     * @param width
     * @param height
     */
    protected void onPreviewDisplaySurfaceChanged(SurfaceHolder holder, int format, int width, int height) {
        // 设置预览大小
        Size viewSize = computeViewSize(width, height);
        Size displaySize = cameraHelper.computeDisplaySizeFromViewSize(viewSize);
        // 根据是否旋转调整预览图像大小
        boolean isCameraRotated = cameraHelper.isCameraRotated();
        converter.setSurfaceTextureAndAttachToGLContext(
                previewFrameTexture,
                isCameraRotated ? displaySize.getHeight() : displaySize.getWidth(),
                isCameraRotated ? displaySize.getWidth() : displaySize.getHeight());
    }

    /**
     * 计算视频图像的最佳的预览大小
     * @param width
     * @param height
     * @return
     */
    protected Size computeViewSize(int width, int height) {
        return new Size(width, height);
    }
    /**
     * 对于手掌是否在识别范围内的判断
     *  当前识别范围设置的是listview所在的constraintview 是因为getTop等函数只能获得相对于控件母view的位置情况
     * @param multiHandLandmarks
     * @return 判断结果
     */
    private boolean isHandInRecZone(List<LandmarkProto.NormalizedLandmarkList> multiHandLandmarks){
        // : 9/8/2022 实现手掌识别范围的限制
        LandmarkProto.NormalizedLandmarkList landmarks = multiHandLandmarks.get(multiHandLandmarks.size() - 1);
        Float y2 = landmarks.getLandmark(9).getY();// 获得中指根部的纵坐标情况
        Float yy=landmarks.getLandmark(0).getY();
        // 当前视频在屏幕上的大小 按照相对于父容器的情况进行计算
        TextView vedio_load_size=findViewById(R.id.no_camera_access_view);
        int vedio_bottom=vedio_load_size.getBottom();
        int vedio_top=vedio_load_size.getTop();
        int vedio_height=vedio_bottom-vedio_top;
        // 获得识别区域控件在屏幕上的坐标
        TextView rec_zone=findViewById(R.id.loginRecArea);
        int rec_zone_bottom=rec_zone.getBottom();
        int rec_zone_top=rec_zone.getTop();
//        Log.d(myTAG, "rec_Zone_top="+rec_zone_top+" rec_zone_bottom"+rec_zone_bottom);
        if(!(yy*vedio_height>rec_zone_top&&yy*vedio_height<rec_zone_bottom&&y2*vedio_height>rec_zone_top&&y2*vedio_height<rec_zone_bottom)){
//            Log.d(myTAG, "当前的手掌不在识别区域内");
//            send_text_to_bundle("当前的手掌不在识别区域内");
            return false;
        }
        else{
            return true;
        }
    }

    /**
     * 手势的处理
     * @param multiHandLandmarks 包含右手21个关键点相关坐标的list
     */
    private void HandleTheHands(List<LandmarkProto.NormalizedLandmarkList> multiHandLandmarks) {
        Runtime runtime = Runtime.getRuntime();
        String title = RecHands.handGestureDiscriminator_Pro(multiHandLandmarks);// 对手掌关键点坐标进行分类得到的结果
        LandmarkProto.NormalizedLandmarkList landmarks = multiHandLandmarks.get(multiHandLandmarks.size() - 1);

//        Log.d(myTAG, "musicontrol当前输出的手势"+title);
        int upper_limit = 25;

        SharedPreferences prefs = PreferenceManager.getDefaultSharedPreferences(this);
        /*
        设置需要做出响应的手势
         */
        string_to_num_map.put("FINISHSIGN", 5);
        float[] temp_arr = {0, 0};
        if(record_flag){
            // 进行手势序列的采集
            for(int i=0;i<n_keypoints;i++){
                Log.d(myTAG, "获得的关键点坐标"+landmarks.getLandmark(i).getX());
                temp21keypoints.get(i).trainingHistory[0].add(landmarks.getLandmark(i).getX());
                temp21keypoints.get(i).trainingHistory[1].add(landmarks.getLandmark(i).getY());
            }
//            float temp_x4=landmarks.getLandmark(4).getX();
//            float temp_y4=landmarks.getLandmark(4).getY();
//            float temp_x8=landmarks.getLandmark(8).getX();
//            float temp_y8=landmarks.getLandmark(8).getY();
//            temp_HandRecord4.trainingHistory[0].add(temp_x4);
//            temp_HandRecord4.trainingHistory[1].add(temp_y4);
//            temp_HandRecord8.trainingHistory[0].add(temp_x8);
//            temp_HandRecord8.trainingHistory[1].add(temp_y8);
        }else{
            if (string_to_num_map.containsKey(title)) {
                // 如果当前的手势是需要进行响应的手势
                int want_the_num = (Integer) string_to_num_map.get(title);
                if (flag_activity == -1 || flag_activity == want_the_num) {
                    array_to_count_activity[want_the_num]++;
                    change_the_bar(array_to_count_activity[want_the_num]);
                } else {
                    flag_activity = want_the_num;
                    array_to_count_activity[want_the_num] = 0;
                    change_the_bar(0);
                }
                for (int i = 0; i < array_to_count_activity.length; i++) {
                    if (i == want_the_num)
                        continue;
                    array_to_count_activity[i] = 0;
                }
                if (array_to_count_activity[want_the_num] == upper_limit) {
                    doAction(want_the_num);
                }
            } else {
                for (int i = 0; i < array_to_count_activity.length; i++) {
                    array_to_count_activity[i] = 0;
                }
                change_the_bar(0);
            }
        }
    }

    /**
     * 修改响应进度条
     * @param change_num
     */
    private void change_the_bar(int change_num) {
        progressBar.setProgress(max(0, min(change_num * 4, 100)));
    }
    @Override
    protected void onPause() {
        super.onPause();
        converter.close();
    }
    protected void onResume() {

        super.onResume();

        initFruits();
        MenuAdapter adapter = new MenuAdapter(this, R.layout.main_menu_ui_item, fruitList);
        ListView listView = (ListView) findViewById(R.id.list_view_login);
        listView.setAdapter(adapter);

        next_song = 0;
        converter = new ExternalTextureConverter(eglManager.getContext());
        converter.setFlipY(FLIP_FRAMES_VERTICALLY);
        converter.setConsumer(processor);
        if (PermissionHelper.cameraPermissionsGranted(this)&&vedio_flag) {
            startCamera();
        }
    }
    // 动态权限获取
    @Override
    public void onRequestPermissionsResult(int requestCode, String[] permissions, int[] grantResults) {

        super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        PermissionHelper.onRequestPermissionsResult(requestCode, permissions, grantResults);
        switch (requestCode) {
            case 222:
                Log.d(myTAG, "app写外存权限申请成功");
                Toast.makeText(getApplicationContext(), "已申请权限", Toast.LENGTH_SHORT).show();
            default:
                super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        }
    }

    /**
     * 启动相机
     */
    public void startCamera() {
        cameraHelper = new CameraXPreviewHelper();
        cameraHelper.setOnCameraStartedListener(this::onCameraStarted);
        // 设置使用的是前置还是后置摄像头
        CameraHelper.CameraFacing cameraFacing =
                USE_FRONT_CAMERA ? CameraHelper.CameraFacing.FRONT : CameraHelper.CameraFacing.BACK;
        cameraHelper.startCamera(this, cameraFacing, null, cameraTargetResolution());
    }

    /**
     * 相机启动后事件
     * @param surfaceTexture
     */
    protected void onCameraStarted(SurfaceTexture surfaceTexture) {
        // 显示预览
        previewFrameTexture = surfaceTexture;
        previewDisplayView.setVisibility(View.VISIBLE);
    }

    /**
     * 设置相机大小
     * @return
     */
    protected Size cameraTargetResolution() {
        return null;
    }

    /**
     * 集中处理按钮的点按响应
     * @param v
     */
    public void onClick(View v)
    {

    }
    /**
     * 将记录的手势序列写到文件中
     */
    public void writeRecord(){
        Log.d(myTAG, "进行写文件的操作");
        try {
            // 文件和路径的创建
            createDir();
            // 新建文件对象
            Log.d(myTAG, "写入文件路径:"+path);
            File file=new File(path,fileName);
            // 创建缓冲对象，实现文件的写入
            BufferedWriter bw = new BufferedWriter(new FileWriter(file, true));
            int i;
//            int lLength=temp_HandRecord4.trainingHistory[0].size();
            int lLength=temp21keypoints.get(0).trainingHistory[0].size();
            // 每个点位包含两个维度的坐标均需要记录
            for(int num_keypoints=0;num_keypoints<n_keypoints;num_keypoints++){
                for(int num_coordinate=0;num_coordinate<2;num_coordinate++){
                    String temp_Record=record_gesture;// 记录的手势的名字
                    // 将list中存在的数据写入
                    for(i=0;i<lLength;i++)
                    {
                        temp_Record+=",";
//                    temp_Record+=temp_HandRecord4.trainingHistory[num_coordinate].get(i).toString();
                        Log.d(myTAG, String.format("关键点序号%d，关键点坐标维度%d,关键点序列位置%d",num_keypoints,num_coordinate,i));
                        temp_Record+=temp21keypoints.get(num_keypoints).trainingHistory[num_coordinate].get(i).toString();
                    }
                    bw.write(temp_Record);// 写入一行，每一列使用逗号隔开
                    bw.newLine();// 行换行
                }
            }
            // 对关键点8序列的记录
//            for(int num_coordinate=0;num_coordinate<2;num_coordinate++){
//                String temp_Record=temp_userName;
//                // 将list中存在的数据写入
//                for(i=0;i<lLength;i++)
//                {
//                    temp_Record+=",";
//                    temp_Record+=temp_HandRecord8.trainingHistory[num_coordinate].get(i).toString();
//                }
//                bw.write(temp_Record);// 写入一行，每一列使用逗号隔开
//                bw.newLine();// 行换行
//            }
            // 缓冲流关闭
            bw.close();
        }
        catch (Exception e)
        {
            e.printStackTrace();
        }
    }
    /*
    检查是否所的权限被获取
    动态获得ACTION_MANAGE_ALL_FILES_ACCESS_PERMISSION对应的权限
     */
    /**
     * 手动检查并获取权限的函数
     */
    public boolean askForPermission(){
        if(Build.VERSION.SDK_INT>=Build.VERSION_CODES.R){
            Log.d(myTAG, "当前安卓系统版本大于11");
            // 如果版本是Android11时候
            if(!Environment.isExternalStorageManager()){
                // 当不能够获得外部存储的情况
                Intent intent=new Intent(Settings.ACTION_MANAGE_ALL_FILES_ACCESS_PERMISSION);
                startActivity(intent);
                return FALSE;
            }
            // 已经获得访问外存的权限
            return TRUE;
        }
        Log.d(myTAG, "当前安卓系统版本不是11");
        return TRUE;
    }
    /**
     * 设定路径和文件创建的函数
     */
    public static void createDir(){
        // 获得路径
        try{
            // 新建文件对象，并设置文件的路径
            File folde=new File(path);
            if (!folde.exists() || !folde.isDirectory())
            {
                // 如果当前路径不存，需要自行创建路径
                Log.i(myTAG, "路径进行对应的创建："+path);
                folde.mkdirs();// 路径创建
            }
            // 新建文件对象，声明文件的类型是csv文件
            File file=new File(path,fileName);
            // 当文件不存在时，需要重新自行创建
            if(!file.exists())
            {
                Log.d(myTAG, "对应文件的创建");
                file.createNewFile();
            }
        }catch (Exception e){
            e.printStackTrace();
        }
    }
}

